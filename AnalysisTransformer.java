import java.util.*;
import soot.*;
import soot.jimple.AnyNewExpr;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JGotoStmt;
import soot.jimple.internal.*;
import soot.jimple.*;
import soot.toolkits.graph.*;
import soot.toolkits.scalar.BackwardFlowAnalysis;
import soot.toolkits.scalar.FlowSet;

class HEAP_OBJECT{
    String obj_name ;
    Map<String, HEAP_OBJECT> obj_pointers_list ;
}

public class AnalysisTransformer extends BodyTransformer {
    
    Map<String, HEAP_OBJECT> stack_map = new HashMap<>() ;
    Set<String> escaping_set = new HashSet<>();
    Map<String, Set<String>> final_map = new HashMap<>();
    int method_count = 0;
    Set<SootClass> classes = new HashSet<>();

    void fetchPointsToObject(HEAP_OBJECT heap_object){
        if(heap_object == null)
            return ;
        escaping_set.add(heap_object.obj_name);
        for(Map.Entry<String, HEAP_OBJECT> entry  : heap_object.obj_pointers_list.entrySet()){
            fetchPointsToObject(entry.getValue());
        }
    }
    
    @Override
    protected void internalTransform(Body body, String phaseName, Map<String, String> options) {
        // Construct CFG for the current method's body
        String thiss  = null;
        stack_map.clear() ;
        escaping_set.clear() ;
        PatchingChain<Unit> units = body.getUnits();
        classes.add(body.getMethod().getDeclaringClass());
        // System.out.println("=========================================" + body.getMethod().getDeclaringClass() + ":" + body.getMethod().getName() + "================================================");
        // Iterate over each unit of CFG.
        // Shown how to get the line numbers if the unit is a "new" Statement.
        Iterator<Unit> unitIt = units.snapshotIterator();
        while (unitIt.hasNext()) {
            Unit u = unitIt.next();
            // System.out.println("Unit is " + u) ;
            // System.out.println("Class of the object: " + u.getClass().getName());

            if(u instanceof JIfStmt){
                IfStmt ifStmt = (IfStmt) u;
                if (ifStmt.getCondition() instanceof JEqExpr) {
                    System.out.println("Equality comparison: " + ifStmt.getCondition());
                    JEqExpr equal_expression = (JEqExpr)ifStmt.getCondition() ;
                    Value left = equal_expression.getOp1();
                    Value right = equal_expression.getOp2();
                    String left_str = left.toString();
                    String right_str = right.toString();
                    System.out.println(left_str);
                    System.out.println(right_str);
                    if(right_str.equals("null")){
                        if(stack_map.containsKey(left_str)){
                            body.getUnits().swapWith(ifStmt, Jimple.v().newNopStmt());
                        }
                        else{
                            GotoStmt newGotoStmt = Jimple.v().newGotoStmt(ifStmt.getTarget());
                            body.getUnits().swapWith(ifStmt, newGotoStmt);
                        }
                    }
                } else if (ifStmt.getCondition() instanceof JNeExpr) {
                    System.out.println("Inequality comparison: " + ifStmt.getCondition());
                    JNeExpr unequal_expression = (JNeExpr)ifStmt.getCondition() ;
                    Value left = unequal_expression.getOp1();
                    Value right = unequal_expression.getOp2();
                    String left_str = left.toString();
                    String right_str = right.toString();
                    System.out.println(left_str);
                    System.out.println(right_str);
                    if(right_str.equals("null")){
                        if(stack_map.containsKey(left_str)){
                            GotoStmt newGotoStmt = Jimple.v().newGotoStmt(ifStmt.getTarget());
                            body.getUnits().swapWith(ifStmt, newGotoStmt);
                        }
                        else{
                            body.getUnits().swapWith(ifStmt, Jimple.v().newNopStmt());   
                        }
                    }
                } else {
                    System.out.println("Other comparison: " + ifStmt.getCondition());
                }
            }
            if(u instanceof JIdentityStmt){
                JIdentityStmt stmt = (JIdentityStmt) u;
                Value left = stmt.getLeftOp();
                Value right = stmt.getRightOp();
                if(right instanceof ThisRef){
                    thiss = left.toString();
                }
                String left_str = left.toString();
                String right_str = right.toString();
                // System.out.println("\t\t" + left_str + "\t" + right_str);
                HEAP_OBJECT obj = new HEAP_OBJECT();
                obj.obj_name = "parameter_object" ;
                obj.obj_pointers_list = new HashMap<>() ;
                stack_map.put(left_str , obj) ;
                // System.out.println("\t\t" + stack_map);
            }
            else if (u instanceof JAssignStmt) {
                JAssignStmt stmt = (JAssignStmt) u;
                Value left = stmt.getLeftOp();
                Value right = stmt.getRightOp();
                String left_str = left.toString();
                String right_str = right.toString();
                // System.out.println("\t\t" + left_str + "\t" + right_str);
                if (right instanceof JNewExpr) {
                    HEAP_OBJECT obj = new HEAP_OBJECT();
                    obj.obj_name = String.valueOf(u.getJavaSourceStartLineNumber()) ;
                    obj.obj_pointers_list = new HashMap<>() ;
                    stack_map.put(left_str , obj) ;
                    // System.out.println("\t\t" + stack_map);
                }
                else if(left instanceof JInstanceFieldRef){
                    JInstanceFieldRef jef = (JInstanceFieldRef)left;
                    Value base_object = jef.getBase();
                    String base_str = base_object.toString() ;
                    String field_str = jef.getField().getName() ;
                    // System.out.println("\t\t" + base_str + "\t" + field_str);
                    if(stack_map.get(base_str) != null){
                        stack_map.get(base_str).obj_pointers_list.put(field_str , stack_map.get(right_str));
                        // System.out.println("\t\t" + stack_map.get(base_str) + " : " + stack_map.get(base_str).obj_pointers_list);
                    }
                }
                else if(right instanceof JInstanceFieldRef){
                    JInstanceFieldRef jef = (JInstanceFieldRef)right;
                    Value base_object = jef.getBase();
                    String base_str = base_object.toString() ;
                    String field_str = jef.getField().getName() ;
                    // System.out.println("\t\t" + base_str + "\t" + field_str);
                    if(stack_map.get(base_str) != null){
                        if(stack_map.get(base_str).obj_pointers_list.get(field_str) == null){
                            HEAP_OBJECT n = new HEAP_OBJECT();
                            n.obj_name = "parameter_object" ;
                            n.obj_pointers_list = new HashMap<>();
                            stack_map.get(base_str).obj_pointers_list.put(field_str, n);
                        }
                        stack_map.put(left_str, stack_map.get(base_str).obj_pointers_list.get(field_str));
                    }
                    else    
                        stack_map.put(left_str, null);
                    // System.out.println("\t\t" + stack_map.get(left_str));
                }
                else if(left instanceof JimpleLocal && right instanceof JimpleLocal){
                    // System.out.println("************************************************************************************************");
                    stack_map.put(left_str, stack_map.get(right_str));
                }
                else if(left instanceof JimpleLocal && right instanceof JCastExpr){
                    // System.out.println("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAaaaa");
                    JCastExpr jcastexpr = (JCastExpr)right ;
                    // System.out.println(jcastexpr.getCastType().toString());
                    // System.out.println(jcastexpr.getOp().toString());
                    stack_map.put(left_str, stack_map.get(jcastexpr.getOp().toString()));
                }
                else if(left instanceof Local && right instanceof VirtualInvokeExpr){
                    VirtualInvokeExpr vexpr = (VirtualInvokeExpr)right ;
                    if(!vexpr.getMethod().getName().contains("init")){
                        Value base = vexpr.getBase();
                        fetchPointsToObject(stack_map.get(base.toString()));
                        List<Value> args = vexpr.getArgs();
                        for(Value x: args) fetchPointsToObject(stack_map.get(x.toString()));
                    }
                }
                else if(left instanceof StaticFieldRef && right instanceof JimpleLocal){
                    fetchPointsToObject(stack_map.get(right_str));
                }
            }

            else if(u instanceof JInvokeStmt){
                JInvokeStmt istmt = (JInvokeStmt)u ;
                if(!istmt.getInvokeExpr().getMethod().getName().contains("init")){
                    List<Value> arguments = istmt.getInvokeExpr().getArgs();
                    if(istmt.getInvokeExpr() instanceof VirtualInvokeExpr){
                            VirtualInvokeExpr vexpr = (VirtualInvokeExpr)istmt.getInvokeExpr();
                            Value base = vexpr.getBase();
                            fetchPointsToObject(stack_map.get(base.toString()));
                    }
                    for(Value x : arguments)
                    {
                        // System.out.println("\t\t" + "Argument is " + x);
                        fetchPointsToObject(stack_map.get(x.toString()));
                        // System.out.println("\t\tESCAPING SET" + escaping_set);
                    }  
                }
            }

            else if(u instanceof JReturnStmt){
                JReturnStmt rstmt = (JReturnStmt)u;
                Value rvalue = rstmt.getOp();
                // System.out.println("\t\tI am return statement and my value is " + rvalue);
                if(!rvalue.toString().equals("null")){
                        fetchPointsToObject(stack_map.get(rvalue.toString()));
                }
                // System.out.println("\t\tESCAPING SET " + escaping_set);
            }

            else if(u instanceof JThrowStmt){
                JThrowStmt jthrowstmt = (JThrowStmt) u ;
                fetchPointsToObject(stack_map.get(jthrowstmt.getOp().toString()));
            }

        }

        for(Value x : body.getParameterLocals())
        {
            fetchPointsToObject(stack_map.get(x.toString()));
        }
        fetchPointsToObject(stack_map.get(thiss));
        
        escaping_set.remove("parameter_object");
        if(!escaping_set.isEmpty()) final_map.put(body.getMethod().getDeclaringClass() + ":" + body.getMethod().getName(), new HashSet<>(escaping_set));
        method_count++ ;
        int total_methods = 0;
        for(SootClass x : classes) total_methods += x.getMethodCount() ;
        if(total_methods == method_count){
            TreeMap<String, Set<String>> sorted_final_map = new TreeMap<>(final_map);
            for(Map.Entry<String, Set<String>> entry  : sorted_final_map.entrySet()){
                System.out.print(entry.getKey() + " ");
                TreeSet<String> sortedSet = new TreeSet<>(entry.getValue());
                for(String x : sortedSet) System.out.print(x + " ");
                System.out.println();
            }
        }
        
    }
}
