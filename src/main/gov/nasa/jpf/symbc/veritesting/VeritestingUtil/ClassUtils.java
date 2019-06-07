package gov.nasa.jpf.symbc.veritesting.VeritestingUtil;

import com.ibm.wala.classLoader.CallSiteReference;
import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAOptions;
import com.ibm.wala.types.MethodReference;
import com.ibm.wala.types.TypeName;
import com.ibm.wala.util.strings.StringStuff;
import gov.nasa.jpf.Config;
import gov.nasa.jpf.symbc.VeritestingListener;
import gov.nasa.jpf.symbc.veritesting.StaticRegionException;
import gov.nasa.jpf.vm.ClassInfo;
import gov.nasa.jpf.vm.ClassInfoException;
import gov.nasa.jpf.vm.ThreadInfo;

import java.io.File;
import java.lang.reflect.Method;
import java.net.MalformedURLException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import static gov.nasa.jpf.symbc.veritesting.VeritestingUtil.ReflectUtil.getSignature;

/**
 * A utility class used during discovering of static regions.
 */
public class ClassUtils {
    public static void addSubClassNames(ThreadInfo ti, ClassHierarchy cha,
                                        HashSet<String> methodSummarySubClassNames, String methodSummaryClassName) {
        Config conf = ti.getVM().getConfig();
        String classPath = conf.getStringArray("classpath")[0] + "/";
        File f = new File(classPath);
        URL[] cp = new URL[0];
        try {
            cp = new URL[]{f.toURI().toURL()};
        } catch (MalformedURLException e) {
            System.out.println("Encountered MalformedURLException with classPath = " + classPath);
            return;
        }
        URLClassLoader urlcl = new URLClassLoader(cp);
        Class cAdditional;
        try {
            cAdditional = urlcl.loadClass(methodSummaryClassName);
        } catch (ClassNotFoundException e) {
            return;
        }
        Method[] allMethodsAdditional;
        try {
            allMethodsAdditional = cAdditional.getDeclaredMethods();
        } catch(NoClassDefFoundError n) {
            System.out.println("NoClassDefFoundError for methodSummaryClassName = "  +methodSummaryClassName);
            System.out.println(n.getMessage());
            return;
        }
        if(allMethodsAdditional.length == 0) return;
        //Only need to add subclass once for all the methods in the class
        Method m = allMethodsAdditional[0];
        String signature = null;
        try {
            signature = ReflectUtil.getSignature(m);
        } catch (StaticRegionException e) {
            return;
        }
        MethodReference mr = StringStuff.makeMethodReference(methodSummaryClassName + "." + signature);
        IMethod iMethod = cha.resolveMethod(mr);
        if (iMethod == null) {
            System.out.println("could not resolve " + mr);
            return;
        }
        IClass iClass = iMethod.getDeclaringClass();
        for(IClass subClass: cha.computeSubClasses(iClass.getReference())) {
            if(iClass.equals(subClass)) continue;
            String subClassName = subClass.getReference().getName().getClassName().toString();
            if(subClass.getReference().getName().getPackage() != null) {
                String packageName = subClass.getReference().getName().getPackage().toString().replaceAll("/", ".");
                subClassName = packageName + "." + subClassName;
            }
            methodSummarySubClassNames.add(subClassName);
        }
    }

    public static void findClasses(ThreadInfo ti, ClassHierarchy cha, String classPath, String startingClassName,
                                   HashSet<String> methodSummaryClassNames) {

        methodSummaryClassNames.add(startingClassName);
        HashSet<String> newClassNames;
        int iteration = 0;
        do {
            newClassNames = new HashSet<>();
            for (String className : methodSummaryClassNames) {

                File f = new File(classPath);
                URL[] cp = new URL[0];
                try {
                    cp = new URL[]{f.toURI().toURL()};
                } catch (MalformedURLException e) {
                    e.printStackTrace();
                }
                URLClassLoader urlcl = new URLClassLoader(cp);
                Class c;
                try {
                    c = urlcl.loadClass(className);
                } catch (ClassNotFoundException e) {
                    continue;
                }
                if(c == null) continue;
                Method[] allMethods;
                try {
                     allMethods = c.getDeclaredMethods();
                } catch (NoClassDefFoundError n) {
                    System.out.println("NoClassDefFoundError for className = " + className + "\n " +
                            n.getMessage());
                    continue;
                }
                for (Method method : allMethods) {
                    String signature = null;
                    try {
                        signature = ReflectUtil.getSignature(method);
                    } catch (StaticRegionException e) {
                        continue;
                    }
                    MethodReference mr = StringStuff.makeMethodReference(className + "." + signature);
                    IMethod iMethod = cha.resolveMethod(mr);
                    if(iMethod == null)
                        continue;
                    AnalysisOptions options = new AnalysisOptions();
                    options.getSSAOptions().setPiNodePolicy(SSAOptions.getAllBuiltInPiNodes());
                    IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
                    IR ir = cache.getIR(iMethod, Everywhere.EVERYWHERE);
                    if(ir == null) {
                        System.out.println("failed to get WALA IR for method: " + className +"." + signature);
                        continue;
                    }
                    Iterator<CallSiteReference> iterator = ir.iterateCallSites();
                    while (iterator.hasNext()) {
                        CallSiteReference reference = iterator.next();
                        MethodReference methodReference = reference.getDeclaredTarget();
                        String declaringClass = methodReference.getDeclaringClass().getName().getClassName().toString();
                        String newClassName = declaringClass;
                        if(methodReference.getDeclaringClass().getName().getPackage() != null) {
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
            for(Iterator it = methodSummaryClassNames.iterator(); it.hasNext();) {
                String methodSummaryClassName = (String) it.next();
                ClassUtils.addSubClassNames(ti, cha, newClassNames, methodSummaryClassName);
            }
            //find veritesting regions inside all the methods discovered so far
            methodSummaryClassNames.addAll(newClassNames);
            System.out.println("iteration = " + iteration);
            ++iteration;
            if (iteration == VeritestingListener.maxStaticExplorationDepth)
                break;
        } while(newClassNames.size() != 0);
    }

    public static ArrayList<String> getSuperClassList(ThreadInfo ti, String className) {
        ArrayList<String> ret = new ArrayList();
        ClassInfo ci;
        try {
            ci = ti.resolveReferencedClass(className);
        } catch(ClassInfoException c) {
            ret.add(className);
            return ret;
        }
        while (ci != null) {
            ret.add(ci.getName());
            ci = ci.getSuperClass();
        }
        return ret;
    }

    public static String getType(TypeName typeName) {
        return typeName.getPackage() != null ? (typeName.getPackage().toString().replace('/', '.') + "." + typeName.getClassName()) : typeName.getClassName().toString();
    }
}
