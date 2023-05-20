/**
 * @id java/examples/detect-log
 * @name pre-log detection dataDep + sideEffect
 * @description test for localflow dataDep and globalflow sideEffect
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
         //加入副作用分析
         or this instanceof MySideEffect
         
     }
 }

 //副作用分析的配置
 class MySideEffectsConfig extends DataFlow::Configuration {
    MySideEffectsConfig() { this = "MySideEffectsConfig" }
  
    //sink是sb.append()
    override predicate isSource(DataFlow::Node source) {
      exists(MethodAccess ma,Method method,VarAccess va,Class c| 
        //source.asExpr()= ma and
        //method.getName().matches("%append%") and
       // ma.getCallee() = method and
        //ma.getCaller() = sb.getCallable()
        //source.asExpr() = sb.getDeclExpr()
        ma.getMethod().getName().matches("%append%") and
        ma.getQualifier().getType()=c and
        (c.getASupertype*().hasQualifiedName("java.lang", "StringBuilder") or
        c.getASupertype*().hasQualifiedName("java.lang", "StringBuffer")) and
        source.asExpr() = ma.getQualifier()
         
      )
    }
    /*
    override predicate isSink(DataFlow::Node sink) {
      exists(MethodAccess call,Expr arg|
        //符合日志调用的条件
        isLogger(call) and
        //日志调用条件里面的参数，这个参数不是String类型的
        arg=call.getAnArgument() and
        not arg instanceof StringLiteral and
        //获取日志调用的表达式
        //call.getQualifier() = sink.asExpr()
        //这句话只能查到xxx.xxx()之前的东西，而且单个的参数也不能查 
        //arg.getAChildExpr()=sink.asExpr() and
        //这句话可以查到xxx.xxx()之后的东西
        arg.getUnderlyingExpr()=sink.asExpr() 
        //and sink.toString().matches("%toString%")
      )
      }  
      */
     override predicate isSink(DataFlow::Node sink) {
        sink.asExpr() instanceof VarAccess
       }
  }
  //副作用分析的结果，改写fws
  //from MySideEffectsConfig config,DataFlow::Node source, DataFlow::Node sink,Stmt s
  //where config.hasFlow(source, sink) and s=source.asExpr().getEnclosingStmt()
  //select s,"path of stringbuilder/buffer" 
  //定义一个stmt类
  class MySideEffect extends Expr{
    MySideEffect(){
        exists(MySideEffectsConfig seconfig, DataFlow::Node sesource, DataFlow::Node sesink|  
            seconfig.hasFlow(sesource, sesink) and this=sesource.asExpr())
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
 select source.getEnclosingStmt(),"prelogstmt localflow dataDep and globalflow sideEffect" 