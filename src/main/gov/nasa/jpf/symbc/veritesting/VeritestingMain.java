package gov.nasa.jpf.symbc.veritesting;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.*;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.ssa.*;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.util.WalaException;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.graph.dominators.Dominators;
import com.ibm.wala.util.graph.dominators.NumberedDominators;
import com.ibm.wala.util.io.FileProvider;
import com.ibm.wala.util.strings.StringStuff;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.CreateStaticRegions;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ClassUtils;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ReflectUtil;
import gov.nasa.jpf.symbc.veritesting.ast.transformations.ssaToAst.StaticRegion;
import gov.nasa.jpf.vm.ThreadInfo;
import x10.wala.util.NatLoop;
import x10.wala.util.NatLoopSolver;

import za.ac.sun.cs.green.expr.Operation;

import static gov.nasa.jpf.symbc.VeritestingListener.exclusionsFile;
import static gov.nasa.jpf.symbc.VeritestingListener.jitAnalysis;

/**
 * Main class file for veritesting static analysis exploration.
 */
public class VeritestingMain {

    public HashSet endingInsnsHash;
    ClassHierarchy cha;
    HashSet<String> methodSummaryClassNames, methodSummarySubClassNames;
    private boolean methodAnalysis = false;
    private String currentPackageName;
    public static HashMap<String, StaticRegion> veriRegions = new HashMap<>();
    public static HashSet<String> skipVeriRegions = new HashSet<>();
    public static final HashSet<String> skipRegionStrings = new HashSet<>();
    private ThreadInfo ti;
    private static HashSet<String> attemptedMethods = new HashSet<>();

    SSACFG cfg;
    HashSet startingPointsHistory;
    String currentClassName, currentMethodName, methodSig;
    HashSet<NatLoop> loops;
    IR ir;

    public VeritestingMain(ThreadInfo ti) {
        try {
            Map map = System.getenv();
            String appJar = System.getenv("TARGET_CLASSPATH_WALA");// + appJar;
            AnalysisScope scope = AnalysisScopeReader.makeJavaBinaryAnalysisScope(appJar,
                    jitAnalysis == true ? null : (new FileProvider()).getFile(exclusionsFile));
//                    (new FileProvider()).getFile(CallGraphTestUtil.REGRESSION_EXCLUSIONS));
            System.out.print("Constructing class hierarchy...");
            cha = ClassHierarchyFactory.make(scope);
            System.out.println("done!");
            methodSummaryClassNames = new HashSet<String>();
            //veritestingRegions = new HashMap<>();
            veriRegions = new HashMap<>();
            this.ti = ti;
        } catch (WalaException | IOException e) {
            e.printStackTrace();
        }
    }

    public static HashSet<String> getAttemptedMethods() {
        return attemptedMethods;
    }

    public void analyzeForVeritesting(ArrayList<String> classPaths, String _className) {
        endingInsnsHash = new HashSet();
        findClasses(ti, cha, classPaths, _className, methodSummaryClassNames);
        startingPointsHistory = new HashSet();
        URL[] cp = new URL[classPaths.size()];
        int cp_index = 0;
        for (String classPath : classPaths) {
            File f = new File(classPath);
            try {
                cp[cp_index++] = f.toURI().toURL();
            } catch (MalformedURLException e) {
                e.printStackTrace();
                continue;
            }
        }

        try {
            URLClassLoader urlcl = new URLClassLoader(cp);
            Class c = urlcl.loadClass(_className);
            Method[] allMethods;
            try {
                allMethods = c.getDeclaredMethods();
            } catch (NoClassDefFoundError n) {
                System.out.println("NoClassDefFoundError for className = " + _className + "\n " +
                        n.getMessage());
                return;
            }
            for (Method m : allMethods) {
                String signature = null;
                try {
                    signature = ReflectUtil.getSignature(m);
                } catch (StaticRegionException e) {
                    continue;
                }
                startAnalysis(getPackageName(_className), _className, signature);
            }

            for (String methodSummaryClassName : methodSummaryClassNames) {
                Class cAdditional;
                try {
                    cAdditional = urlcl.loadClass(methodSummaryClassName);
                } catch (ClassNotFoundException e) {
                    continue;
                }
                Method[] allMethodsAdditional;
                try {
                    allMethodsAdditional = cAdditional.getDeclaredMethods();
                } catch (NoClassDefFoundError n) {
                    System.out.println("NoClassDefFoundError for className = " + methodSummaryClassName + "\n " +
                            n.getMessage());
                    continue;
                }
                for (Method m : allMethodsAdditional) {
                    String signature = null;
                    try {
                        signature = ReflectUtil.getSignature(m);
                    } catch (StaticRegionException e) {
                        continue;
                    }
                    startAnalysis(getPackageName(methodSummaryClassName), methodSummaryClassName, signature);
                }
            }
            //Return if not in highOrder mode or higher
            if (VeritestingListener.veritestingMode <= 2) return;
            //summarize methods inside all methods discovered so far
            methodAnalysis = true;
            for (String methodSummaryClassName : methodSummaryClassNames) {
                Class cAdditional;
                try {
                    cAdditional = urlcl.loadClass(methodSummaryClassName);
                } catch (ClassNotFoundException e) {
                    continue;
                }
                Method[] allMethodsAdditional;
                try {
                    allMethodsAdditional = cAdditional.getDeclaredMethods();
                } catch (NoClassDefFoundError n) {
                    System.out.println("NoClassDefFoundError for className = " + methodSummaryClassName + "\n " +
                            n.getMessage());
                    continue;
                }
                for (Method m : allMethodsAdditional) {
                    String signature = null;
                    try {
                        signature = ReflectUtil.getSignature(m);
                    } catch (StaticRegionException e) {
                        continue;
                    }
                    startAnalysis(getPackageName(methodSummaryClassName), methodSummaryClassName, signature);
                }
            }
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }
    }


    private void jitStartAnalysis(String packageName, String className, String methodSig, boolean multiPathAnalysis) throws StaticRegionException {
        MethodReference mr = StringStuff.makeMethodReference(className + "." + methodSig);
        IMethod m = cha.resolveMethod(mr);
        if (m == null) {
            System.out.println("could not resolve " + className + "." + methodSig);
            return;
            //Assertions.UNREACHABLE("could not resolve " + mr);
        }
        AnalysisOptions options = new AnalysisOptions();
        options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
        IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
        ir = cache.getIR(m, Everywhere.EVERYWHERE);
        if (ir == null) {
            System.out.println("Null IR for " + className + "." + methodSig);
            return;
        }
        cfg = ir.getControlFlowGraph();
        currentPackageName = packageName;
        currentClassName = className;
        currentMethodName = m.getName().toString();
        this.methodSig = methodSig.substring(methodSig.indexOf('('));
        System.out.println("Starting " + (methodAnalysis ? "method " : "region ") + "analysis for " +
                currentMethodName + "(" + currentClassName + "." + methodSig + ")");
        NumberedDominators<ISSABasicBlock> uninverteddom =
                (NumberedDominators<ISSABasicBlock>) Dominators.make(cfg, cfg.entry());
        loops = new HashSet<>();
        HashSet<Integer> visited = new HashSet<>();
        NatLoopSolver.findAllLoops(cfg, uninverteddom, loops, visited, cfg.getNode(0));
        // Here is where the magic happens.
        CreateStaticRegions regionCreator = new CreateStaticRegions(ir, loops);
        if (multiPathAnalysis) {
            regionCreator.createStructuredConditionalRegions(veriRegions);
            //regionCreator.createStructuredMethodRegion(veriRegions);
        } else
            regionCreator.jitCreateStructuredRegion(veriRegions);

       /* // Placeholder for testing and visualizing static-time transformations
            Set<String> keys = veriRegions.keySet();
            for (String key: keys) {
                StaticRegion r = veriRegions.get(key);
                PhiToGammaSubstitution sub = new PhiToGammaSubstitution(r);
                sub.doSubstitution();
            } */

    }


    public void jitAnalyzeForVeritesting(ArrayList<String> classPaths, String _className, String jvmMethodName, boolean multiPathRegion) throws StaticRegionException {
        endingInsnsHash = new HashSet();
        //methodSummaryClassNames.add(_className);
        //findClasses(ti, cha, classPaths, _className, methodSummaryClassNames);
        startingPointsHistory = new HashSet();
        URL[] cp = new URL[classPaths.size()];
        int cp_index = 0;
        for (String classPath : classPaths) {
            File f = new File(classPath);
            try {
                cp[cp_index++] = f.toURI().toURL();
            } catch (MalformedURLException e) {
                e.printStackTrace();
                continue;
            }
        }

        try {
            URLClassLoader urlcl = new URLClassLoader(cp);
            Class c = urlcl.loadClass(_className);
            Method[] allMethods;
            try {
                allMethods = c.getDeclaredMethods();
            } catch (NoClassDefFoundError n) {
                System.out.println("NoClassDefFoundError for className = " + _className + "\n " +
                        n.getMessage());
                return;
            }
            for (Method m : allMethods) {
                String signature = null;

                signature = ReflectUtil.getSignature(m);
                String jvmSignature = _className + "." + signature;
                if (jvmSignature.contains(jvmMethodName)) {
                    jitStartAnalysis(getPackageName(_className), _className, signature, multiPathRegion);
                    break;
                }
            }
        } catch (ClassNotFoundException e) {
            e.printStackTrace();
        }


    }


    private String getPackageName(String c) {
        if (c.contains(".")) return c.substring(0, c.lastIndexOf("."));
        else return null;
    }

    public static void findClasses(ThreadInfo ti, ClassHierarchy cha, ArrayList<String> classPaths, String startingClassName,
                                   HashSet<String> methodSummaryClassNames) {

        methodSummaryClassNames.add(startingClassName);
        HashSet<String> newClassNames;
        int iteration = 0;
        URL[] cp = new URL[classPaths.size()];
        int cp_index = 0;
        for (String classPath : classPaths) {
            File f = new File(classPath);
            try {
                cp[cp_index++] = f.toURI().toURL();
            } catch (MalformedURLException e) {
                e.printStackTrace();
                continue;
            }
        }
        do {
            newClassNames = new HashSet<>();
            for (String className : methodSummaryClassNames) {
                URLClassLoader urlcl = new URLClassLoader(cp);
                Class c;
                try {
                    c = urlcl.loadClass(className);
                } catch (ClassNotFoundException e) {
                    continue;
                }
                if (c == null) continue;
                Method[] allMethods;
                try {
                    allMethods = c.getDeclaredMethods();
                } catch (NoClassDefFoundError n) {
                    System.out.println("NoClassDefFoundError for className = " + className + "\n " +
                            n.getMessage());
                    continue;
                }
                for (Method method : allMethods) {
                    String signature;
                    try {
                        signature = ReflectUtil.getSignature(method);
                    } catch (StaticRegionException e) {
                        continue;
                    }
                    MethodReference mr = StringStuff.makeMethodReference(className + "." + signature);
                    IMethod iMethod = cha.resolveMethod(mr);
                    if (iMethod == null)
                        continue;
                    AnalysisOptions options = new AnalysisOptions();
                    options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
                    IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
                    IR ir = cache.getIR(iMethod, Everywhere.EVERYWHERE);
                    if (ir == null) {
                        System.out.println("failed to get WALA IR for method: " + className + "." + signature);
                        continue;
                    }
                    Iterator<CallSiteReference> iterator = ir.iterateCallSites();
                    while (iterator.hasNext()) {
                        CallSiteReference reference = iterator.next();
                        MethodReference methodReference = reference.getDeclaredTarget();
                        String declaringClass = methodReference.getDeclaringClass().getName().getClassName().toString();
                        String newClassName = declaringClass;
                        if (methodReference.getDeclaringClass().getName().getPackage() != null) {
                            String packageName =
                                    methodReference.getDeclaringClass().getName().getPackage().toString().replace("/", ".");
                            newClassName = packageName + "." + newClassName;
                        }
                        if (!methodSummaryClassNames.contains(newClassName)) {
                            newClassNames.add(newClassName);
                        }
                    }
                }
            }
            methodSummaryClassNames.addAll(newClassNames);
            for (Iterator it = methodSummaryClassNames.iterator(); it.hasNext(); ) {
                String methodSummaryClassName = (String) it.next();
                ClassUtils.addSubClassNames(ti, cha, newClassNames, methodSummaryClassName);
            }
            //find veritesting regions inside all the methods discovered so far
            methodSummaryClassNames.addAll(newClassNames);
            System.out.println("iteration = " + iteration);
            ++iteration;
            if (iteration == VeritestingListener.maxStaticExplorationDepth)
                break;
        } while (newClassNames.size() != 0);
    }


    private void startAnalysis(String packageName, String className, String methodSig) {
        try {

            MethodReference mr = StringStuff.makeMethodReference(className + "." + methodSig);
            IMethod m = cha.resolveMethod(mr);
            if (m == null) {
                System.out.println("could not resolve " + className + "." + methodSig);
                return;
                //Assertions.UNREACHABLE("could not resolve " + mr);
            }
            AnalysisOptions options = new AnalysisOptions();
            options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
            IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
            ir = cache.getIR(m, Everywhere.EVERYWHERE);
            if (ir == null) {
                System.out.println("Null IR for " + className + "." + methodSig);
                return;
            }
            cfg = ir.getControlFlowGraph();
            currentPackageName = packageName;
            currentClassName = className;
            currentMethodName = m.getName().toString();
            this.methodSig = methodSig.substring(methodSig.indexOf('('));
            System.out.println("Starting " + (methodAnalysis ? "method " : "region ") + "analysis for " +
                    currentMethodName + "(" + currentClassName + "." + methodSig + ")");
            NumberedDominators<ISSABasicBlock> uninverteddom =
                    (NumberedDominators<ISSABasicBlock>) Dominators.make(cfg, cfg.entry());
            loops = new HashSet<>();
            HashSet<Integer> visited = new HashSet<>();
            NatLoopSolver.findAllLoops(cfg, uninverteddom, loops, visited, cfg.getNode(0));
            // Here is where the magic happens.
            CreateStaticRegions regionCreator = new CreateStaticRegions(ir, loops);
            attemptedMethods.add(this.methodSig);

            if (!methodAnalysis) {
                //regionCreator.createStructuredConditionalRegions(cfg, veritestingRegions);
                regionCreator.createStructuredConditionalRegions(veriRegions);
            } else {
                if (!currentMethodName.equals("NoVeritest")) {
                    //regionCreator.createStructuredMethodRegion(cfg, veritestingRegions);
                    regionCreator.createStructuredConditionalRegions(veriRegions);
                    regionCreator.createStructuredMethodRegion(veriRegions);
                }
            }
            /* // Placeholder for testing and visualizing static-time transformations
            Set<String> keys = veriRegions.keySet();
            for (String key: keys) {
                StaticRegion r = veriRegions.get(key);
                PhiToGammaSubstitution sub = new PhiToGammaSubstitution(r);
                sub.doSubstitution();
            } */

        } catch (Exception e) {
            e.printStackTrace();
        }
    }


    private Operation.Operator negateOperator(Operation.Operator operator) {
        switch (operator) {
            case NE:
                return Operation.Operator.EQ;
            case EQ:
                return Operation.Operator.NE;
            case GT:
                return Operation.Operator.LE;
            case GE:
                return Operation.Operator.LT;
            case LT:
                return Operation.Operator.GE;
            case LE:
                return Operation.Operator.GT;
            default:
                System.out.println("Don't know how to negate Green operator (" + operator + ")");
                return null;
        }
    }


}

