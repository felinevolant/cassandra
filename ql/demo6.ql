/**
 * @id java/examples/detect-log
 * @name pre-log detection dataDep+ctrlDep
 * @description test for localflow dataDep/ctrlDep
 * @problem.severity warning
 * @kind problem
 */

 import java
 
 import java
 import semmle.code.java.ControlFlowGraph
 import semmle.code.java.dataflow.DataFlow
 import semmle.code.java.dataflow.TaintTracking
 import semmle.code.java.dataflow.FlowSources
 import semmle.code.java.StringFormat

 //判断是否是日志调用的谓词
 predicate isLogger(MethodAccess call) {
  exists(Method method|call.getMethod() = method and
  method.getDeclaringType().hasQualifiedName("org.slf4j", "Logger") and 
  not method.getName().matches("%Enabled"))
}

//尝试用这种方式
class Plc extends boolean{
  Plc(){
    this=true or
    this=false
  }
}

class WorkList extends boolean{
  WorkList(){
    this=true or
    this=false 
  }
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
      this instanceof VarAccess or
      //尝试数据依赖的定义
      //An update of a variable or an initialization of the variable.
      this instanceof VariableUpdate or
      this instanceof VariableAssign or
      //扩大数据依赖范围
      this instanceof VarAccess
      
      
  }
}

Stmt doDataDepAnalysis(IsSource source,IsSink sink){
  //把demo3的select from where改写成一个谓词
  exists( | 
    DataFlow::localFlow(DataFlow::exprNode(source), DataFlow::exprNode(sink)) 
    and not sink=source | 
    result=source.getEnclosingStmt() )
}

//基于控制依赖
 //source的定义，source是if stmt 或者 switch stmt
 class CtrlDepSource extends Expr{
  CtrlDepSource(){
   
    (
    this.getEnclosingStmt() instanceof IfStmt or
    this.getEnclosingStmt() instanceof SwitchStmt or
    this.getEnclosingStmt() instanceof ConditionalStmt
    )
    and
    (
      this instanceof VarAccess or
      this instanceof VariableAssign or
      this instanceof VariableUpdate
    )
  }
}

//sink的定义
//sink是基于数据依赖的结果
class CtrlDepSink extends ControlFlowNode{
  CtrlDepSink(){
    exists( IsSink sink,IsSource source,Stmt datadepStmt| 
      datadepStmt=doDataDepAnalysis(source,sink) and
      datadepStmt.getControlFlowNode()=this)
  }
}

//写一个谓词把ctrl和data结合起来
Stmt doCtrlDepAnalysis(CtrlDepSource csource,CtrlDepSink csink){
  //把demo6原来的fws改写
  exists( IfStmt stmt| 
    csource.getBasicBlock().getABBSuccessor()=csink.getBasicBlock() | 
    //csource.getEnclosingStmt()和csink都是prelog
    result=csource.getEnclosingStmt() or
    result=csink  
    )
}

//把then语句也加进来
Stmt addThenStmt(CtrlDepSource csource,CtrlDepSink csink){
  exists( IfStmt stmt| 
    csource.getBasicBlock().getABBSuccessor()=csink.getBasicBlock() and
    csource.getEnclosingStmt() instanceof IfStmt| 
    //csource.getEnclosingStmt()和csink都是prelog
    stmt=csource.getEnclosingStmt() and
    (result=stmt.getThen() or result=stmt.getElse())
    
  )  
   
}

//添加logging guards语句
predicate isLogGuard(MethodAccess call) {
  exists(Method method | 
    call.getMethod() = method and
    (
    method.getName().matches("%isDebugEnabled%") or 
    method.getName().matches("%isTraceEnabled%") 
    ) 
  )
}
Stmt addGuardsStmt(){
  exists(IfStmt ifstmt,MethodAccess ma,Stmt stmt|  
    ifstmt.getCondition()=ma and 
    isLogGuard(ma) and
    (
      ifstmt.getThen()=stmt or
      ifstmt.getElse()=stmt or
      ifstmt=stmt
    ) and
    result=stmt
    )
}



//根据demo5进行改写
//from CtrlDepSource csource,CtrlDepSink csink

//where csource.getBasicBlock().getABBSuccessor()=csink.getBasicBlock()
//csource.getEnclosingStmt()和csink都是prelog
//select csource,csink,csource.getEnclosingStmt()

from CtrlDepSource csource,CtrlDepSink csink,Stmt prelog,Stmt prelog2,Stmt prelog3,IfStmt ifstm
where (doCtrlDepAnalysis(csource,csink) = prelog or addThenStmt(csource,csink)=prelog)

//条件语句的then也应该是prelog
and 
(
    if
    prelog instanceof IfStmt
    then 
    ifstm=prelog and 
    (
    prelog2=ifstm.getThen() or
    prelog2=ifstm.getElse() or
    prelog2=prelog
    )
    else prelog2=prelog
)
and (prelog2=prelog3 or addGuardsStmt()=prelog3)
select prelog3,"prelogstmt datadep and ctldep"