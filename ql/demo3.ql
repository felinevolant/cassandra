/**
 * @id java/examples/detect-log
 * @name pre-log detection dataDep
 * @description test for localflow dataDep
 * @kind problem
 * @problem.severity warning
 */

import java
import semmle.code.java.ControlFlowGraph
import semmle.code.java.dataflow.DataFlow
import semmle.code.java.dataflow.DefUse
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.dataflow.FlowSources
import semmle.code.java.StringFormat

//判断是否是日志调用的谓词
predicate isLogger(MethodAccess call) {
    exists(Method method|call.getMethod() = method and
    method.getDeclaringType().hasQualifiedName("org.slf4j", "Logger") and 
    not method.getName().matches("%Enabled"))
}


//尝试使用局部数据流分析,局部数据流分析应该就属于数据依赖了
class IsSink extends Expr{
    IsSink(){
        exists(MethodAccess call,Expr arg|
            //符合日志调用的条件
            isLogger(call) and
            //日志调用条件里面的参数，这个参数不是String类型的
            arg=call.getAnArgument() and
            not arg instanceof StringLiteral and
    
            //这句话可以查到xxx.xxx()之后的东西
            arg.getUnderlyingExpr()=this
          )
    }
}
//从youtube学到的定义日志调用的方法写sink
class IsSink2 extends Expr{
    IsSink2(){
        this=any(LoggerFormatMethod l).getAReference().getAnArgument() and
        not this instanceof StringLiteral
    }
}

class IsSource extends Expr{
    IsSource(){
        //this instanceof VarAccess or
        //尝试数据依赖的定义
        //An update of a variable or an initialization of the variable.
        this instanceof VariableUpdate or
        this instanceof VariableAssign or
        this instanceof VarAccess
        
        
    }
}

//局部数据流分析
from IsSink2 sink, IsSource source,Stmt s
where DataFlow::localFlow(DataFlow::exprNode(source), DataFlow::exprNode(sink)) and
not sink=source 
//and
//尝试数据依赖的定义,这句话加不加都是一样的
//defUsePair(source, sink) and
//s=source.getEnclosingStmt()
//select source,sink,"prelogstmt datadep"
//只输出source
//select source,"prelogstmt datadep"
//输出source所在的stmt
select source.getEnclosingStmt(),"prelogstmt datadep"
