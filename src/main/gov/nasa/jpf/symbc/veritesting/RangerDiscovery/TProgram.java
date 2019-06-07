package gov.nasa.jpf.symbc.veritesting.RangerDiscovery;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.DiscoveryUtil;
import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput.InOutManager;
import jkind.lustre.*;
import jkind.lustre.parsing.LustreParseUtil;
import jkind.lustre.visitors.AstVisitor;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;


/**
 * This class holds the T program, that can be used for either the counter Example step or the synthesis step.
 */
public class TProgram extends Ast {
    public final List<TypeDef> types;
    public final List<Constant> constants;
    public final List<Function> functions;
    public final List<Node> nodes;

    /**
     * Generates a T program counter example step from a file path, usually this is done in the first time.
     *
     * @return
     */
    public TProgram(String tFileName) {
        super(Location.NULL);
        String programStr = null;
        try {
            programStr = new String(Files.readAllBytes(Paths.get(tFileName)), "UTF-8");

        } catch (IOException e) {
            System.out.println("Problem reading file. " + e.getMessage());
        }

        Program program = LustreParseUtil.program(programStr);

        List<TypeDef> types = new ArrayList<>();
        List<Constant> constants = new ArrayList<>();
        List<Function> functions = new ArrayList<>();
        List<Node> nodes = new ArrayList<>();

        types.addAll(program.types);
        constants.addAll(program.constants);
        functions.addAll(program.functions);
        nodes.addAll(changeMainToTnode(program.nodes, program.main));
        this.types = types;
        this.constants = constants;
        this.functions = functions;
        this.nodes = nodes;

    }

    public Node generateMainNode(Node tNode, Node wrapperNode, InOutManager inOutManager) {
        List<Expr> wrapperArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        List<Expr> tNodeArgs = (List<Expr>) (List<?>) DiscoveryUtil.varDeclToIdExpr(tNode.inputs);
        wrapperArgs.remove(wrapperArgs.size()-1);
        Expr callRwapper = new NodeCallExpr("R_wrapper", wrapperArgs);
        tNodeArgs.set(tNodeArgs.size() - 1, callRwapper);
        NodeCallExpr callT = new NodeCallExpr("T_node", (List<Expr>) tNodeArgs);
        assert (tNode.outputs.size() == 1); //assuming a single output is possible for TNode to indicate constraints are
        // passing
        VarDecl mainOut = new VarDecl("out", tNode.outputs.get(0).type);
        List mainOutList = new ArrayList();
        mainOutList.add(mainOut);
        Equation mainEq = new Equation(DiscoveryUtil.varDeclToIdExpr(mainOut), callT);
        List mainEquations = new ArrayList();
        mainEquations.add(mainEq);
        return new Node("main", tNode.inputs, mainOutList, null, mainEquations, null, null, null, null,
                null);

    }

    private List<? extends Node> changeMainToTnode(List<Node> nodes, String main) {
        List<Node> newNodes = new ArrayList<>();
        for (int i = 0; i < nodes.size(); i++) {
            if (nodes.get(i).id.equals(main)) {
                Node tnode = generateTnode(nodes.get(i));
                newNodes.addAll(nodes.subList(i + 1, nodes.size()));
                newNodes.add(tnode);
                return newNodes;
            }
            newNodes.add(nodes.get(i));
        }

        System.out.println("cannot find main to convert to T.");
        assert false;
        return null;
    }

    private Node generateTnode(Node node) {
        return new Node("T_node", node.inputs, node.outputs, node.locals, node.equations, node.properties, node
                .assertions, node.realizabilityInputs, node.contract, node.ivc);
    }
/*
    public TProgram createSynthesisProg(){

    }*/

    @Override
    public String toString() {
        return super.toString();
    }

    @Override
    public <T, S extends T> T accept(AstVisitor<T, S> visitor) {
        return visitor.visit(new Program(Location.NULL, types, constants, functions, nodes, "T_node"));
    }
}
