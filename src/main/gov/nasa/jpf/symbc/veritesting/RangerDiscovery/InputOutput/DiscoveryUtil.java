package gov.nasa.jpf.symbc.veritesting.RangerDiscovery.InputOutput;

import gov.nasa.jpf.symbc.veritesting.RangerDiscovery.DiscoverContract;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.Pair;
import gov.nasa.jpf.symbc.veritesting.VeritestingUtil.StatisticManager;
import jkind.lustre.*;
import za.ac.sun.cs.green.expr.Operation;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import static jkind.lustre.UnaryOp.NEGATIVE;
import static jkind.lustre.UnaryOp.NOT;

public class DiscoveryUtil {
    public static NamedType stringToLusterType(String typeName) {
        if (typeName.equals("int"))
            return NamedType.INT;
        else if (typeName.equals("float"))
            return NamedType.REAL;
        else if (typeName.equals("boolean"))
            return NamedType.BOOL;
        /*else if (typeName.equals("string"))
            return lusterStringType;*/
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static BinaryOp rangerBinaryOptoLusterOp(String s) {
        BinaryOp op;

        if (s.equals("!="))
            op = BinaryOp.fromString("<>");
        else if (s.equals("=="))
            op = BinaryOp.fromString("=");
        else if (s.equals("&&"))
            op = BinaryOp.fromString("and");
        else if (s.equals("||"))
            op = BinaryOp.fromString("or");
        else
            op = BinaryOp.fromString(s);

        return op;
    }


    public static UnaryOp rangerUnaryyOptoLusterOp(String s) {
        UnaryOp op = null;

        if (s.equals("!"))
            op = UnaryOp.fromString("not");

        return op;
    }


    public static UnaryOp toLustreUnaryOp(Operation.Operator operator) {
        if (operator.toString().equals("-"))
            return NEGATIVE;
        else if (operator.toString().equals("!"))
            return NOT;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static BinaryOp toLustreBinaryOp(Operation.Operator operator) {
        if (operator == Operation.Operator.ADD)
            return BinaryOp.PLUS;
        else if (operator == Operation.Operator.SUB)
            return BinaryOp.MINUS;
        if (operator == Operation.Operator.MUL)
            return BinaryOp.MULTIPLY;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.DIVIDE;
        else if (operator == Operation.Operator.EQ)
            return BinaryOp.EQUAL;
        else if (operator == Operation.Operator.DIV)
            return BinaryOp.INT_DIVIDE;
        else if (operator == Operation.Operator.NE)
            return BinaryOp.NOTEQUAL;
        else if (operator == Operation.Operator.GT)
            return BinaryOp.GREATER;
        else if (operator== Operation.Operator.LT)
            return BinaryOp.LESS;
        else if (operator == Operation.Operator.GE)
            return BinaryOp.GREATEREQUAL;
        else if (operator == Operation.Operator.LE)
            return BinaryOp.LESSEQUAL;
        else if (operator == Operation.Operator.OR)
            return BinaryOp.OR;
        else if (operator == Operation.Operator.AND)
            return BinaryOp.AND;
        else {
            System.out.println("unknown type!");
            assert false;
        }
        return null;
    }

    public static List<IdExpr> varDeclToIdExpr(List<VarDecl> varDeclList){
        ArrayList<IdExpr> idExprList = new ArrayList<>();

        for(int i=0; i< varDeclList.size() ; i++){
            idExprList.add(new IdExpr(varDeclList.get(i).id));
        }

        return idExprList;
    }

    public static IdExpr varDeclToIdExpr(VarDecl varDecl){
        return new IdExpr(varDecl.id);
    }


    public static boolean writeToFile(String fileName, String content){
        fileName = DiscoverContract.folderName + "/" + fileName;
        try (Writer writer = new BufferedWriter(new OutputStreamWriter(
                new FileOutputStream(fileName), "utf-8"))) {
            writer.write(content);
        }
        catch (FileNotFoundException e){
            System.out.println("unable to write to file!");
            e.printStackTrace();
        } catch (IOException e) {
            System.out.println("unable to write to file!");
            e.printStackTrace();
        }
        return true;
    }


    public static Pair<VarDecl, Equation> replicateToOut(VarDecl varDecl, String stringName){
        VarDecl newVarDecl = new VarDecl(stringName, varDecl.type);

        Equation eq = new Equation(varDeclToIdExpr(newVarDecl), varDeclToIdExpr(varDecl));

        return new Pair(newVarDecl, eq);
    }
}
