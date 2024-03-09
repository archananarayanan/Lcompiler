import ast
from ast import *
from graph import *
from priority_queue import PriorityQueue
from utils import * 
from x86_ast import *
import os
import copy
from typing import Tuple as TupleTyping, List, Set, Dict


Binding = TupleTyping[Name, expr]
Temporaries = List[Binding]
MAX_REG = 100

class Compiler:
    
    stack_space = {}
    root_stack = {}
    used_callee = {}
    unused_callee = {}
    arg_regs = [Reg("rdi"), Reg("rsi"), Reg("rdx"), Reg("rcx"), Reg("r8"), Reg("r9")]
    varTypes = {}
    tupleColors = []
    varColors = []
    callee_save = [Reg("rsp"), Reg("rbp"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"), Reg("r15")]
    free_ptr = GlobalValue(label_name('free_ptr'))
    fromspace_end = GlobalValue(label_name('fromspace_end'))
    global_free_ptr = Global(label_name('free_ptr'))
    global_fromspace_end = Global(label_name('fromspace_end'))
    global_vars = {}
    functions = []
    lambda_functions = []
    free_var_types = {}
    fun_freeVars = {}
    unescaped_functions = []


    def getGlobal(self, name):
         if name == "fromspace_end":
              return self.global_fromspace_end
         if name == "free_ptr":
              return self.global_free_ptr
         else:
              if name not in self.global_vars.keys():
                   self.global_vars[name] = Global(name)
              return self.global_vars[name]

    

    ############################################################################
    # Shrink the Lif 
    ############################################################################
    
    def shrink_exp(self, s: expr) -> expr:
          match s:
                case IfExp(test, body, orelse):
                    res = self.shrink_exp(test)
                    body_exp = self.shrink_exp(body)
                    or_exp = self.shrink_exp(orelse)
                    return IfExp(res, body_exp, or_exp)
                case BoolOp(And(), values):
                    left = values[0]; right = values[1]
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return IfExp(l, r, Constant(False))
                case BoolOp(Or(), values):
                    left = values[0]; right = values[1]
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return IfExp(l, Constant(True), r)
                case UnaryOp(Not(), v):
                    val = self.shrink_exp(v)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.shrink_exp(v)
                    return UnaryOp(USub(), v)
                case BinOp(left, Add(), right):
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    return s
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    es_s = []
                    for e in es:
                         es_s.append(self.shrink_exp(e))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    t_s = self.shrink_exp(tup)
                    n_s = self.shrink_exp(index)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.shrink_exp(tup)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return s
                case Lambda(var, exp):
                    exp_s = self.shrink_exp(exp)
                    return Lambda(var, exp_s)
                case Call(Name('arity'), [exp]):
                    t_s = self.shrink_exp(exp)
                    return Call(Name('arity'), [t_s])
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Call(func, args):
                    shrink_fun = self.shrink_exp(func)
                    shrink_args = []
                    for ag in args:
                         shrink_args.append(self.shrink_exp(ag))
                    return Call(shrink_fun, shrink_args)
                case _ :
                    raise Exception('error in shrink exp, unexpected ' + repr(s)) 
               
    def shrink_stmt(self, s: stmt) -> stmt:
        print("received shrink stmt- ", [s])
        match s:
            case If(test, body, orelse):
                res = self.shrink_exp(test)
                body_exp = []
                for b in body:
                     body_exp.append(self.shrink_stmt(b))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.shrink_stmt(o))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.shrink_stmt(arg)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.shrink_stmt(value)
                return Expr(val)
            case Assign([Name(id)], value):
                val = self.shrink_stmt(value)
                return Assign([Name(id)], val)
            case While(exp, stmts, []):
                  cond_shrink = self.shrink_exp(exp)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.shrink_stmt(x))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Assign([Subscript(tup, index, Store())], value):
                    tup_s = self.shrink_exp(tup)
                    index_s = self.shrink_exp(index)
                    val_s = self.shrink_exp(value)
                    return Assign([Subscript(tup_s, index_s, Store())], val_s)
            case AnnAssign(var, type, exp, simple):
                    exp_s = self.shrink_exp(exp)
                    return AnnAssign(var, type, exp_s, simple)
            case Return(value):
                    exp_value = self.shrink_exp(value)
                    return Return(exp_value)
            case FunctionDef(name, params, bod, dl, returns, comment):
                    shrink_stmts = []
                    for s in bod:
                         shrink_stmts.append(self.shrink_stmt(s))
                    return FunctionDef(name, params, shrink_stmts, dl, returns, comment)
            case _:
                return self.shrink_exp(s)
              
    def create_main_function(self, stmts: List[stmt]) -> FunctionDef:
         stmts.append(Return(Constant(0)))
         def_stmt = FunctionDef('main', [], stmts, None, IntType(), None)
         self.functions.append('main')
         return def_stmt
    
    def shrink(self, p):
            match p:
                case Module(body):
                    res = [] 
                    toplevel_stmts = []
                    for x in body:
                        match x:
                             case FunctionDef(name, params, bod, dl, returns, comment):
                                  res.append(self.shrink_stmt(x))
                                  if name not in self.functions:
                                       self.functions.append(name)
                             case _:
                                  toplevel_stmts.append(self.shrink_stmt(x))
                    res.append(self.create_main_function(toplevel_stmts))
                    for x in res:
                         print([x])
                    return Module(res)
                case _ :
                    raise Exception('error in shrink main module, unexpected ' + repr(p))

    ############################################################################
    # uniquify
    ############################################################################

    def uniquify_exp(self, s: expr, uniquify_vars, lambda_vars, isLambda) -> expr:
         match s:
                case IfExp(test, body, orelse):
                    res = self.uniquify_exp(test, uniquify_vars, lambda_vars, isLambda)
                    body_exp = self.uniquify_exp(body, uniquify_vars, lambda_vars, isLambda)
                    or_exp = self.uniquify_exp(orelse, uniquify_vars, lambda_vars, isLambda)
                    return IfExp(res, body_exp, or_exp)
                case UnaryOp(Not(), v):
                    val = self.uniquify_exp(v, uniquify_vars, lambda_vars, isLambda)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.uniquify_exp(v, uniquify_vars, lambda_vars, isLambda)
                    return UnaryOp(USub(), val)
                case BinOp(left, Add(), right):
                    l = self.uniquify_exp(left, uniquify_vars, lambda_vars, isLambda)
                    r = self.uniquify_exp(right, uniquify_vars, lambda_vars, isLambda)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.uniquify_exp(left, uniquify_vars, lambda_vars, isLambda)
                    r = self.uniquify_exp(right, uniquify_vars, lambda_vars, isLambda)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.uniquify_exp(left, uniquify_vars, lambda_vars, isLambda)
                    r = self.uniquify_exp(right, uniquify_vars, lambda_vars, isLambda)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    if id not in self.functions:
                         if isLambda and id in lambda_vars.keys():
                              return Name(lambda_vars[id])
                         elif isLambda and id not in lambda_vars.keys():
                              if id in uniquify_vars.keys():
                                   lambda_vars[id] = uniquify_vars[id] #the same variable is used in lambda
                                   return Name(uniquify_vars[id])
                              if id not in uniquify_vars.keys():
                                   temp = generate_name(id)
                                   lambda_vars[id] = temp
                                   return Name(temp)
                         elif not isLambda and id not in uniquify_vars.keys():
                              temp = generate_name(id)
                              uniquify_vars[id] = temp
                              return Name(temp)
                         elif not isLambda and id in uniquify_vars.keys():
                              return Name(uniquify_vars[id])
                    return s
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    es_s = []
                    for e in es:
                         es_s.append(self.uniquify_exp(e, uniquify_vars, lambda_vars, isLambda))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    t_s = self.uniquify_exp(tup, uniquify_vars, lambda_vars, isLambda)
                    n_s = self.uniquify_exp(index, uniquify_vars, lambda_vars, isLambda)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.uniquify_exp(tup, uniquify_vars, lambda_vars, isLambda)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return s
                case Lambda(var, exp):
                    new_var = []
                    lambda_vars = {} # creating a new cache for lambda vars
                    for x in var:
                         temp = generate_name(x)
                         lambda_vars[x] = temp
                         new_var.append(temp)
                    exp_s = self.uniquify_exp(exp, uniquify_vars, lambda_vars, True)
                    return Lambda(new_var, exp_s)
                case Call(Name('arity'), [exp]):
                    t_s = self.uniquify_exp(exp, uniquify_vars, lambda_vars, isLambda)
                    return Call(Name('arity'), [t_s])
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Call(func, args):
                    shrink_fun = self.uniquify_exp(func, uniquify_vars, lambda_vars, isLambda)
                    shrink_args = []
                    for ag in args:
                         shrink_args.append(self.uniquify_exp(ag, uniquify_vars, lambda_vars, isLambda))
                    return Call(shrink_fun, shrink_args)
                case _ :
                    raise Exception('error in uniquify exp, unexpected ' + s) 
               
    def uniquify_stmt(self, s: stmt, uniquify_vars, lambda_vars) -> stmt:
        match s:
            case If(test, body, orelse):
                res = self.uniquify_exp(test, uniquify_vars, lambda_vars, False)
                body_exp = []
                for b in body:
                     body_exp.append(self.uniquify_stmt(b, uniquify_vars, lambda_vars))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.uniquify_stmt(o, uniquify_vars, lambda_vars))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.uniquify_stmt(arg, uniquify_vars, lambda_vars)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.uniquify_stmt(value, uniquify_vars, lambda_vars)
                return Expr(val)
            case Assign([Name(id)], value):
                if id not in uniquify_vars.keys():
                    temp = generate_name(id)
                    uniquify_vars[id] = temp
                    lhs = Name(temp)
                else:
                    lhs = Name(uniquify_vars[id])
                val = self.uniquify_stmt(value, uniquify_vars, lambda_vars)
                return Assign([lhs], val)
            case While(exp, stmts, []):
                  cond_shrink = self.uniquify_exp(exp, uniquify_vars, lambda_vars, False)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.uniquify_stmt(x, uniquify_vars, lambda_vars))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Assign([Subscript(tup, index, Store())], value):
                    tup_s = self.uniquify_exp(tup, uniquify_vars, lambda_vars, False)
                    val_s = self.uniquify_exp(value, uniquify_vars, lambda_vars, False)
                    return Assign([Subscript(tup_s, index, Store())], val_s)
            case AnnAssign(var, type, exp, simple):
                    lhs = self.uniquify_exp(var, uniquify_vars, lambda_vars, False)
                    exp_s = self.uniquify_exp(exp, uniquify_vars, lambda_vars, False)
                    return AnnAssign(lhs, type, exp_s, simple)
            case Return(value):
                    exp_value = self.uniquify_exp(value, uniquify_vars, lambda_vars, False)
                    return Return(exp_value)
            case FunctionDef(name, params, bod, dl, returns, comment):
                    shrink_stmts = []
                    for s in bod:
                         shrink_stmts.append(self.uniquify_stmt(s, uniquify_vars, lambda_vars))
                    return FunctionDef(name, params, shrink_stmts, dl, returns, comment)
            case _:
                return self.uniquify_exp(s, uniquify_vars, lambda_vars, False)
    
    def uniquify(self, p):
            match p:
                case Module(body):
                    final_res = []
                    for x in body:
                        match x:
                             case FunctionDef(name, params, bod, dl, returns, comment):
                                  res = []
                                  uniquify_vars = {}
                                  new_params = []
                                  for p in params:
                                        temp = generate_name(p[0])
                                        uniquify_vars[p[0]] = temp # generate new var names for function params
                                        new_params.append((temp, p[1]))
                                  for bd in bod:
                                        res.append(self.uniquify_stmt(bd, uniquify_vars, {}))
                                  final_res.append(FunctionDef(name, new_params, res, dl, returns, comment))
                    return Module(final_res)
                case _ :
                    raise Exception('error in shrink main module, unexpected ' + repr(p))

   

    ############################################################################
    # Reveal Functions
    ############################################################################ 
        
    def reveal_exp(self, s: expr, inCall= False, inArgs= False, fun_params= []) -> expr:
          match s:
                case IfExp(test, body, orelse):
                    res = self.reveal_exp(test, inCall, inArgs, fun_params)
                    body_exp = self.reveal_exp(body, inCall, inArgs, fun_params)
                    or_exp = self.reveal_exp(orelse, inCall, inArgs, fun_params)
                    return IfExp(res, body_exp, or_exp)
                case UnaryOp(Not(), v):
                    val = self.reveal_exp(v, inCall, inArgs, fun_params)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.reveal_exp(v, inCall, inArgs, fun_params)
                    return UnaryOp(USub(), v)
                case BinOp(left, Add(), right):
                    l = self.reveal_exp(left, inCall, inArgs, fun_params)
                    r = self.reveal_exp(right, inCall, inArgs, fun_params)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.reveal_exp(left, inCall, inArgs, fun_params)
                    r = self.reveal_exp(right, inCall, inArgs, fun_params)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.reveal_exp(left, inCall, inArgs, fun_params)
                    r = self.reveal_exp(right, inCall, inArgs, fun_params)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    if id not in fun_params:
                         if not inArgs and id in self.functions:
                              return FunRef(id, 0)
                         if inArgs and id in self.functions:
                              return FunRef(id, 0)
                    return s
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    # use a list for mutability
                    es_s = []
                    for e in es:
                         es_s.append(self.reveal_exp(e, inCall, inArgs, fun_params))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    t_s = self.reveal_exp(tup, inCall, inArgs, fun_params)
                    n_s = self.reveal_exp(index, inCall, inArgs, fun_params)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.reveal_exp(tup,inCall, inArgs, fun_params)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return s
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Lambda(var, exp):
                    exp_s = self.reveal_exp(exp)
                    return Lambda(var, exp_s)
                case Call(Name('arity'), [exp]):
                    t_s = self.reveal_exp(exp)
                    return Call(Name('arity'), [t_s])
                case Call(func, args):
                    shrink_fun = self.reveal_exp(func, True, False, fun_params)
                    shrink_fun.arity = len(args) # can we set the airty here ? !!
                    shrink_args = []
                    for ag in args:
                         shrink_args.append(self.reveal_exp(ag, True, True, fun_params= fun_params))
                    return Call(shrink_fun, shrink_args)
                case _ :
                    raise Exception('error in reveal exp, unexpected ' + repr(s)) 
               
    def reveal_stmt(self, s: stmt, fun_params: list) -> stmt:
        match s:
            case If(test, body, orelse):
                res = self.reveal_exp(test, fun_params= fun_params)
                body_exp = []
                for b in body:
                     body_exp.append(self.reveal_stmt(b, fun_params))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.reveal_stmt(o, fun_params))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.reveal_exp(arg, fun_params= fun_params)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.reveal_exp(value, fun_params= fun_params)
                return Expr(val)
            case Assign([Name(id)], value):
                val = self.reveal_exp(value, fun_params= fun_params)
                return Assign([Name(id)], val)
            case While(exp, stmts, []):
                  cond_shrink = self.reveal_exp(exp, fun_params= fun_params)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.reveal_stmt(x, fun_params))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Return(e):
                    return Return(self.reveal_exp(e, fun_params= fun_params))
            case Assign([Subscript(tup, index, Store())], value):
                    tup_s = self.reveal_exp(tup, fun_params= fun_params)
                    index_s = self.reveal_exp(index, fun_params= fun_params)
                    val_s = self.reveal_exp(value, fun_params= fun_params)
                    return Assign([Subscript(tup_s, index_s, Store())], val_s)
            case AnnAssign(var, type, exp, simple):
                    exp_s = self.reveal_exp(exp)
                    return AnnAssign(var, type, exp_s, simple)
            case Return(value):
                    reveal_val = self.reveal_exp(value, fun_params= fun_params)
                    return Return(reveal_val)
            case FunctionDef(name, params, bod, dl, returns, comment):
                    fun_params = []
                    if name not in self.functions:
                         self.functions.append(name)
                    for x in params:
                         fun_params.append(x[0])
                    shrink_stmts = []
                    for s in bod:
                         shrink_stmts.append(self.reveal_stmt(s, fun_params))
                    return FunctionDef(name, params, shrink_stmts, dl, returns, comment)
            case _:
                return self.reveal_exp(s, False, False, fun_params)
    
    def reveal_functions(self, p):
            match p:
                case Module(body):
                    res = []
                    for x in body:
                        res.append(self.reveal_stmt(x, []))
                    return Module(res)
                case _ :
                    raise Exception('error in reveal main module, unexpected ' + repr(p))


    ############################################################################
    # Convert Assignments
    ############################################################################ 
    
    def get_exp_variables(self, s:expr):
         res = set()
         match s:
              case IfExp(test, body, orelse):
                    cnd_res = self.get_exp_variables(test)
                    body_exp = self.get_exp_variables(body)
                    or_exp = self.get_exp_variables(orelse)
                    for x in cnd_res:
                         res.add(x)
                    for x in body_exp:
                         res.add(x)
                    for x in or_exp:
                         res.add(x)
              case UnaryOp(Not(), v):
                    val = self.get_exp_variables(v)
                    for x in val:
                         res.add(x)
              case UnaryOp(USub(), v):
                    val = self.get_exp_variables(v)
                    for x in val:
                         res.add(x)
              case BinOp(left, Add(), right):
                    l = self.get_exp_variables(left)
                    r = self.get_exp_variables(right)
                    for x in l:
                         res.add(x)
                    for x in r:
                         res.add(x)
              case BinOp(left, Sub(), right):
                    l = self.get_exp_variables(left)
                    r = self.get_exp_variables(right)
                    for x in l:
                         res.add(x)
                    for x in r:
                         res.add(x)
              case Compare(left, [cmp], [right]):
                    l = self.get_exp_variables(left)
                    r = self.get_exp_variables(right)
                    for x in l:
                         res.add(x)
                    for x in r:
                         res.add(x)
              case Constant(value):
                    pass
              case Name(id):
                    res.add(s) #add all variables to result set
              case Call(Name('input_int'), []):
                    pass
              case Tuple(es, Load()):
                    es_s = []
                    for e in es:
                         es_s.append(self.get_exp_variables(e))
                         for x in es_s:
                              res.add(x)
              case Subscript(tup, index, Load()):
                    res.add(tup) #adding subscript expressions in the lamba variables ? 
              case Call(Name('len'), [tup]):
                    t_s = self.get_exp_variables(tup)
                    for x in t_s:
                         res.add(x)
              case FunRef(id, arity):
                    pass
              case Lambda(var, exp):
                    exp_s = self.get_exp_variables(exp)
                    for x in exp_s:
                         res.add(x)
              case Call(Name('arity'), [exp]):
                    t_s = self.get_exp_variables(exp)
                    for x in t_s:
                         res.add(x)
              case Allocate(length, typ):
                    pass
              case GlobalValue(name):
                    pass
              case Call(func, args):
                    pass
              case _ :
                    raise Exception('error in shrink exp, unexpected ' + repr(s)) 
           
         return res
    
    def get_lambda_variables(self, s: expr):
         exp_vars = []
         match s:
              case Lambda(var, exp):
                   exp_vars = self.get_exp_variables(exp)
                   for x in var:
                        if Name(x) in exp_vars:
                             exp_vars.discard(Name(x))
              case _:
                   pass
         return exp_vars
    
    def get_lambda_Stmtvariables(self, st: stmt):
         lambda_vars = set()
         match st:
            case If(test, body, orelse):
                lambda_vars.update(self.get_lambda_variables(test))
                for b in body:
                     lambda_vars.update(self.get_lambda_Stmtvariables(b))
                for o in orelse:
                     lambda_vars.update(self.get_lambda_Stmtvariables(o))
            case Expr(Call(Name('print'), [arg])):
                lambda_vars.update(self.get_lambda_variables(arg))
            case Expr(value):
                lambda_vars.update(self.get_lambda_Stmtvariables(value))
            case Assign([Name(id)], value):
                lambda_vars.update(self.get_lambda_variables(value))
            case While(exp, stmts, []):
                  lambda_vars.update(self.get_lambda_variables(exp))
                  for x in stmts:
                    lambda_vars.update(self.get_lambda_Stmtvariables(x))
            case Collect(size):
                    pass
            case Assign([Subscript(tup, index, Store())], value):
                    lambda_vars.add(tup)
                    lambda_vars.update(self.get_lambda_variables(value))
            case AnnAssign(var, type, exp, simple):
                    lambda_vars.update(self.get_lambda_variables(exp))
            case Return(value):
                    lambda_vars.update(self.get_lambda_variables(value))
            case FunctionDef(name, params, bod, dl, returns, comment):
                    shrink_stmts = []
                    for s in bod:
                         lambda_vars.update(self.get_lambda_Stmtvariables(s))
            case _:
                lambda_vars.update(self.get_lambda_variables(s))
    
         return lambda_vars

    def get_assignment_variables(self, s: stmt):
         assgn_vars = set()
         match s:
            case If(test, body, orelse):
                for b in body:
                     assgn_vars.update(self.get_assignment_variables(b))
                for o in orelse:
                     assgn_vars.update(self.get_assignment_variables(o))
            case Expr(Call(Name('print'), [arg])):
                pass
            case Expr(value):
                pass
            case Assign([Name(id)], value):
                assgn_vars.add(Name(id))
                self.free_var_types[Name(id)] = self.get_returnType(value)
            case While(exp, stmts, []):
                  for x in stmts:
                    assgn_vars.update(self.get_assignment_variables(x))
            case Collect(size):
                    pass
            case Assign([Subscript(tup, index, Store())], value):
                    assgn_vars.add(tup) # can we access subscript this way?
                    self.free_var_types[tup] = self.get_returnType(value)
            case AnnAssign(var, typ, exp, simple):
                    pass
            case Return(value):
                    pass
            case _:
                assgn_vars.update(self.get_assignment_variables(s))

         return assgn_vars
    
    
    def free_variables(self, p):
         match p:
              case FunctionDef(name, params, bod, dl, returns, comment):
                    lambda_vars = set(); assgn_vars = set(); freeVar_dict = {}
                    for bd in bod:
                         lambda_vars.update(self.get_lambda_Stmtvariables(bd))
                         assgn_vars.update(self.get_assignment_variables(bd))
                    self.fun_freeVars[name] = assgn_vars
                    free_vars = lambda_vars.intersection(assgn_vars)
                    for x in params:
                         self.free_var_types[Name(x[0])] = x[1]
                    for x in free_vars:
                         freeVar_dict[x] = None
                    return freeVar_dict
              case _ :
                    raise Exception('error in shrink main module, unexpected ' + repr(p))
    
    def convert_exp(self, s: expr, free_vars) -> expr:
         match s:
                case IfExp(test, body, orelse):
                    res = self.convert_exp(test, free_vars)
                    body_exp = self.convert_exp(body, free_vars)
                    or_exp = self.convert_exp(orelse, free_vars)
                    return IfExp(res, body_exp, or_exp)
                case UnaryOp(Not(), v):
                    val = self.convert_exp(v, free_vars)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.convert_exp(v, free_vars)
                    return UnaryOp(USub(), v)
                case BinOp(left, Add(), right):
                    l = self.convert_exp(left, free_vars)
                    r = self.convert_exp(right, free_vars)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.convert_exp(left, free_vars)
                    r = self.convert_exp(right, free_vars)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.convert_exp(left, free_vars)
                    r = self.convert_exp(right, free_vars)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    if Name(id) in free_vars.keys():
                         lhs = free_vars[Name(id)]
                         lhs_stmt = Subscript(lhs, Constant(0), Load())
                    else:
                         lhs_stmt = Name(id)
                    return lhs_stmt
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    es_s = []
                    for e in es:
                         es_s.append(self.convert_exp(e, free_vars))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    if tup in free_vars.keys():
                         lhs = free_vars[tup]
                         lhs_stmt = Subscript(lhs, Constant(0), Load())
                    else:
                         lhs_stmt = Subscript(tup, index, Load())
                    return lhs_stmt
                case Call(Name('len'), [tup]):
                    t_s = self.convert_exp(tup, free_vars)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return s
                case Lambda(var, exp):
                    exp_s = self.convert_exp(exp, free_vars)
                    return Lambda(var, exp_s)
                case Call(Name('arity'), [exp]):
                    t_s = self.convert_exp(exp, free_vars)
                    return Call(Name('arity'), [t_s])
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Call(func, args):
                    shrink_fun = self.convert_exp(func, free_vars)
                    shrink_args = []
                    for ag in args:
                         shrink_args.append(self.convert_exp(ag, free_vars))
                    return Call(shrink_fun, shrink_args)
                case _ :
                    raise Exception('error in shrink exp, unexpected ' + repr(s)) 
               
    def convert_stmt(self, s: stmt, free_vars) -> stmt:
        match s:
            case If(test, body, orelse):
                res = self.convert_exp(test, free_vars)
                body_exp = []
                for b in body:
                     body_exp.append(self.convert_stmt(b, free_vars))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.convert_stmt(o, free_vars))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.convert_stmt(arg, free_vars)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.convert_stmt(value, free_vars)
                return Expr(val)
            case Assign([Name(id)], value):
                val = self.convert_exp(value, free_vars)
                if Name(id) in free_vars.keys():
                     lhs = free_vars[Name(id)]
                     lhs_stmt = Subscript(lhs, Constant(0), Store())
                else:
                     lhs_stmt = Name(id)
                return Assign([lhs_stmt], val)
            case While(exp, stmts, []):
                  cond_shrink = self.convert_exp(exp, free_vars)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.convert_stmt(x, free_vars))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Assign([Subscript(tup, index, Store())], value):
                    val_s = self.convert_exp(value, free_vars)
                    if tup in free_vars.keys():
                         lhs = free_vars[tup]
                         lhs_stmt = Subscript(lhs, Constant(0), Store())
                    else:
                         lhs_stmt = Subscript(tup, index, Store())
                    return Assign([lhs], val_s)
            case AnnAssign(var, type, exp, simple):
                    exp_s = self.convert_exp(exp, free_vars)
                    return AnnAssign(var, type, exp_s, simple)
            case Return(value):
                    exp_value = self.convert_exp(value, free_vars)
                    return Return(exp_value)
            case FunctionDef(name, params, bod, dl, returns, comment):
                    shrink_stmts = []
                    for s in bod:
                         shrink_stmts.append(self.convert_stmt(s, free_vars))
                    return FunctionDef(name, params, shrink_stmts, dl, returns, comment)
            case _:
                return self.convert_exp(s, free_vars)
    
    def check_if_param(self, params, cur):
         for p in params:
              if p[0] == cur.id:
                   return True
         return False
    
    def convert_assignments(self, p):
            match p:
                case Module(body):
                    final_res = []
                    for x in body:
                        match x:
                             case FunctionDef(name, params, bod, dl, returns, comment):
                                  free_vars = self.free_variables(x)
                                  res = []
                                  for y in free_vars.keys():
                                       if not self.check_if_param(params, y):
                                            res.append(Assign([y],Tuple([Uninitialized(self.free_var_types[y])], Load()))) # creating tuple for all free variables
                                            free_vars[y] = y
                                            self.free_var_types[y] = TupleType([self.free_var_types[y]])
                                       else:
                                             tmp = generate_name(y.id.split(".")[0])
                                             res.append(Assign([Name(tmp)],Tuple([y], Load())))
                                             res.append(Assign([Name(tmp)],Tuple([Uninitialized(self.free_var_types[y])], Load()))) # creating tuple for all free variables
                                             free_vars[y] = Name(tmp)
                                             self.free_var_types[Name(tmp)] = TupleType([self.free_var_types[y]])
                                  for bd in bod:
                                        res.append(self.convert_stmt(bd, free_vars))
                                  final_res.append(FunctionDef(name, params, res, dl, returns, comment))
                    return Module(final_res)
                case _ :
                    raise Exception('error in shrink main module, unexpected ' + repr(p))

    
    ############################################################################
    # Challenge 9.2 - Check Escaping Functions 
    ############################################################################ 

           
    def check_escapeFunction_exp(self, s: expr, inCall= False, inArgs= False, fun_params= []) -> expr:
          match s:
                case IfExp(test, body, orelse):
                    self.check_escapeFunction_exp(test)
                    self.check_escapeFunction_exp(body)
                    self.check_escapeFunction_exp(orelse)
                case UnaryOp(Not(), v):
                    self.check_escapeFunction_exp(v)
                case UnaryOp(USub(), v):
                    self.check_escapeFunction_exp(v)
                case BinOp(left, Add(), right):
                    self.check_escapeFunction_exp(left)
                    self.check_escapeFunction_exp(right)
                case BinOp(left, Sub(), right):
                    self.check_escapeFunction_exp(left)
                    self.check_escapeFunction_exp(right)
                case Compare(left, [cmp], [right]):
                    self.check_escapeFunction_exp(left)
                    self.check_escapeFunction_exp(right)
                case Constant(value):
                    pass
                case Name(id):
                    pass
                case Call(Name('input_int'), []):
                    pass
                case Tuple(es, Load()):
                    for e in es:
                         self.check_escapeFunction_exp(e)
                case Subscript(tup, index, Load()):
                    self.check_escapeFunction_exp(tup)
                    self.check_escapeFunction_exp(index)
                case Call(Name('len'), [tup]):
                    self.check_escapeFunction_exp(tup)
                case FunRef(id, arity):
                    if id in self.unescaped_functions:
                         self.unescaped_functions.remove(id)
                case Allocate(length, typ):
                    pass
                case Uninitialized(ty):
                    pass
                case GlobalValue(name):
                    pass
                case Lambda(var, exp):
                    self.check_escapeFunction_exp(exp)
                case Call(Name('arity'), [exp]):
                    self.check_escapeFunction_exp(exp)
                case Call(func, args):
                    pass
                case _ :
                    raise Exception('error in checking functions exp, unexpected ' + repr(s)) 
               
    def check_escapeFunction_stmt(self, s: stmt) -> stmt:
        match s:
            case If(test, body, orelse):
                self.check_escapeFunction_exp(test)
                for b in body:
                     self.check_escapeFunction_stmt(b)
                for o in orelse:
                     self.check_escapeFunction_stmt(o)
            case Expr(Call(Name('print'), [arg])):
                self.check_escapeFunction_exp(arg)
            case Expr(value):
                self.check_escapeFunction_exp(value)
            case Assign([Name(id)], value):
                self.check_escapeFunction_exp(value)
            case While(exp, stmts, []):
                  self.check_escapeFunction_exp(exp)
                  for x in stmts:
                    self.check_escapeFunction_stmt(x)
            case Collect(size):
                    pass
            case Return(e):
                    self.check_escapeFunction_exp(e)
            case Assign([Subscript(tup, index, Store())], value):
                    self.check_escapeFunction_exp(tup)
                    self.check_escapeFunction_exp(value)
            case AnnAssign(var, ty, exp, simple):
                    self.check_escapeFunction_exp(exp)
            case Return(value):
                    self.check_escapeFunction_exp(value)
            case FunctionDef(name, params, bod, dl, returns, comment):
                    if type(returns) == FunctionType:
                         if name in self.unescaped_functions:
                              self.unescaped_functions.remove(name) #if the fn returns Callable, its most likely to be called again
                    for s in bod:
                         self.check_escapeFunction_stmt(s)
            case _:
                self.check_escapeFunction_exp(s)
    
    def check_escape_functions(self, p):
            self.unescaped_functions = self.functions #assigning all functions as unescaped
            match p:
                case Module(body):
                    for x in body:
                        self.check_escapeFunction_stmt(x)
                case _ :
                    raise Exception('error in check fns main module, unexpected ' + repr(p))


    

    ############################################################################
    # Closure Conversion
    ############################################################################ 

    def update_type_Annotations(self, t: Type):
         match t:
              case FunctionType(params, rt):
                   new_params = [TupleType([])]
                   for x in params:
                        new_params.append(self.update_type_Annotations(x))
                   new_ret = self.update_type_Annotations(rt)
                   return TupleType([FunctionType(new_params, new_ret)])
              case _:
                   return t 
              
    def get_closureParam(self, fvs: list):
         lhs = generate_name('fvs')
         tuple_types = [Bottom()] #defining the function type
     #     print("fvs in closure param-", fvs)
     #     print("self free vars - ", self.free_var_types)
         for x in fvs:
              tuple_types.append(self.update_type_Annotations(self.free_var_types[x]))
         return (lhs,TupleType(tuple_types)), Name(lhs) #how do we return a arg ? 
    
    def get_returnType(self, e: expr) -> Type:
     #     print("received type-", e)
         match e:
                case IfExp(test, body, orelse):
                    return self.get_returnType(body) # any one should be suffice ? 
                case UnaryOp(Not(), v):
                    return self.get_returnType(v)
                case UnaryOp(USub(), v):
                    return self.get_returnType(v)
                case BinOp(left, Add(), right):
                    return IntType()
                case BinOp(left, Sub(), right):
                    return IntType()
                case Compare(left, [cmp], [right]):
                    return BoolType()
                case Constant(value):
                    return IntType()
                case Name(id):
                    return IntType()
                case Call(Name('input_int'), []):
                    # return FunctionType([], IntType())
                    return IntType()
                case Tuple(es, Load()):
                   param_types = []
                   for x in es:
                        param_types.append(self.get_returnType(x))
                   return TupleType([param_types])
                case Subscript(tup, index, Load()):
                    return IntType()
                case Subscript(tup, index):
                   return IntType()
                case Call(Name('len'), [tup]):
                    return IntType()
                case FunRef(id, arity):
                    return FunctionType([Bottom()], IntType())
                case Allocate(length, typ):
                    return None
                case GlobalValue(name):
                    return None
                case Lambda(var, exp):
                    return FunctionType([Bottom()], IntType()) #not sure how do we handle it ?
                case Call(Name('arity'), [exp]):
                    return FunctionType([], IntType())
                case Call(func, args):
                   return FunctionType([Bottom()], IntType()) #how do we handle calls to functions
                case _ :
                    raise Exception('error in get return Type , unexpected ' + repr(e)) 
    
    def create_lambda_functions(self, free_vars: list, params: list,exp: expr, name):
         stmts = []
         arg_param, lhs = self.get_closureParam(free_vars)
         new_params = [arg_param]
         for x in params:
              new_params.append(x)
         fun_stmts = []
         for i in range(len(free_vars)):
            stmts.append(Assign([free_vars[i]], Subscript(lhs, Constant(i+1), Load())))
         stmts.append(Return(exp))
         ret_type = self.update_type_Annotations(self.get_returnType(exp)) # to keep up with anotations
         def_stmt = FunctionDef(name, new_params, stmts, None, ret_type, None)
         self.lambda_functions.append(def_stmt)
         

    def closure_exp(self, s: expr, asg: set) -> expr:
          match s:
                case IfExp(test, body, orelse):
                    res = self.closure_exp(test, asg)
                    body_exp = self.closure_exp(body, asg)
                    or_exp = self.closure_exp(orelse, asg)
                    return IfExp(res, body_exp, or_exp)
                case UnaryOp(Not(), v):
                    val = self.closure_exp(v, asg)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.closure_exp(v, asg)
                    return UnaryOp(USub(), v)
                case BinOp(left, Add(), right):
                    l = self.closure_exp(left, asg)
                    r = self.closure_exp(right, asg)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.closure_exp(left, asg)
                    r = self.closure_exp(right, asg)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.closure_exp(left, asg)
                    r = self.closure_exp(right, asg)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    return s
                case Uninitialized(ty):
                    return s
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    es_s = []
                    for e in es:
                         es_s.append(self.closure_exp(e, asg))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    t_s = self.closure_exp(tup, asg)
                    n_s = self.closure_exp(index, asg)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.closure_exp(tup, asg)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return Closure(arity, [s])
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Lambda(var, exp):
                    lambda_name = generate_name('lambda')
                    fvs = list(self.get_lambda_variables(s))
                    print("fvs from get lambda methos -", fvs)
                    n = len(var)
                    params = [FunRef(lambda_name, n)]
                    params.extend(fvs)
                    var_type = []
                    for x in var:
                         var_type.append((x, IntType())) #how do we find the type of lambda var ?? 
                    self.create_lambda_functions(fvs, var_type, exp, lambda_name)
                    return Closure(n, params)
                case Call(Name('arity'), [exp]):
                    t_s = self.closure_exp(exp, asg)
                    return Call(Name('arity'), [t_s])
                case Call(func, args):
                    if type(func) == FunRef and func.name in self.unescaped_functions:
                         return Call(func, args) # challenge 9.2
                    else:
                         shrink_fun = self.closure_exp(func, asg)
                         begin_stmts = []
                         cls_tmp = Name(generate_name('clos'))
                         begin_stmts.append(Assign([cls_tmp], shrink_fun))
                         args_exp = [cls_tmp]
                         for x in args:
                              args_exp.append(self.closure_exp(x, asg))
                         ret_begin = Call(Subscript(cls_tmp, Constant(0), Load()), args_exp)
                         return Begin(begin_stmts, ret_begin)
                case _ :
                    raise Exception('error in closure exp, unexpected ' + repr(s)) 
         
    def closure_stmt(self, s: stmt, asg: set) -> stmt:
        match s:
            case If(test, body, orelse):
                res = self.closure_exp(test, asg)
                body_exp = []
                for b in body:
                     body_exp.append(self.closure_stmt(b, asg))
                or_exp = []
                for o in orelse:
                     or_exp.append(self. closure_stmt(o, asg))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.closure_exp(arg, asg)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.closure_exp(value, asg)
                return Expr(val)
            case Assign([Name(id)], value):
                val = self.closure_exp(value, asg)
                return Assign([Name(id)], val)
            case While(exp, stmts, []):
                  cond_shrink = self.closure_exp(exp, asg)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.closure_stmt(x, asg))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Return(e):
                    return Return(self.closure_exp(e, asg))
            case AnnAssign(var, type, exp, simple):
                    exp_s = self.closure_exp(exp, asg)
                    return Assign([var], exp_s)
            case Assign([Subscript(tup, index, Store())], value):
                    tup_s = self.closure_exp(tup, asg)
                    val_s = self.closure_exp(value, asg)
                    return Assign([Subscript(tup_s, index, Store())], val_s)
            case _:
                return self.closure_exp(s, asg)      
    
    def convert_to_closures(self, p):
            match p:
                case Module(body):
                    t_fun = [] 
                    functions = []
                    self.check_escape_functions(p) #to identify escaped functions
                    print("unescaped functions -", self.unescaped_functions)
                    for x in body:
                        match x:
                             case FunctionDef(name, params, bod, dl, returns, comment):
                                  if name in self.unescaped_functions:
                                       new_params = params
                                       ret_type = returns
                                  else:
                                       arg_params, lhs = self.get_closureParam([])
                                       new_params = [arg_params]
                                       for x in params:
                                             new_params.append(x)
                                       ret_type = self.update_type_Annotations(returns)

                                  fun_stmts = []
                                  for b in bod:
                                        fun_stmts.append(self.closure_stmt(b, self.fun_freeVars[name]))
                                        
                                  t_fun.append(FunctionDef(name, new_params, fun_stmts, dl, ret_type, comment))

                    for fun in self.lambda_functions:
                         functions.append(fun)
                    for fun in t_fun:
                         if t_fun not in functions:
                              functions.append(fun)
                    return Module(functions)
                case _ :
                    raise Exception('error in limit main module, unexpected ' + repr(p))
    
    
    ############################################################################
    # Limit Functions
    ############################################################################ 
               
    def limit_exp(self, limit_ref: list, s: expr) -> expr:
          match s:
                case IfExp(test, body, orelse):
                    res = self.limit_exp(limit_ref, test)
                    body_exp = self.limit_exp(limit_ref, body)
                    or_exp = self.limit_exp(limit_ref, orelse)
                    return IfExp(res, body_exp, or_exp)
                case BoolOp(And(), values):
                    i=0
                    res = []
                    left = values[0]; right = values[1]
                    l = self.limit_exp(limit_ref, left)
                    r = self.limit_exp(limit_ref, right)
                    return IfExp(l, r, Constant(False))
                case BoolOp(Or(), values):
                    i=0
                    res = []
                    left = values[0]; right = values[1]
                    l = self.limit_exp(limit_ref, left)
                    r = self.limit_exp(limit_ref, right)
                    return IfExp(l, Constant(True), r)
                case UnaryOp(Not(), v):
                    val = self.limit_exp(limit_ref, v)
                    return (UnaryOp(Not(), val))
                case UnaryOp(USub(), v):
                    val = self.limit_exp(limit_ref, v)
                    return UnaryOp(USub(), v)
                case BinOp(left, Add(), right):
                    l = self.limit_exp(limit_ref, left)
                    r = self.limit_exp(limit_ref, right)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.limit_exp(limit_ref, left)
                    r = self.limit_exp(limit_ref, right)
                    return BinOp(l , Sub(), r)
                case Compare(left, [cmp], [right]):
                    l = self.limit_exp(limit_ref, left)
                    r = self.limit_exp(limit_ref, right)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return s
                case Name(id):
                    if id in limit_ref:
                         k = limit_ref.index(id)
                         return Subscript(Name('tup'), Constant(k), Load()) # tuple access
                    else:
                         return s
                case Call(Name('input_int'), []):
                    return s
                case Tuple(es, Load()):
                    # use a list for mutability
                    es_s = []
                    for e in es:
                         es_s.append(self.limit_exp(limit_ref, e))
                    return Tuple(es_s, Load())
                case Begin(stmts, res):
                    res_limit = self.limit_exp(limit_ref, res)
                    stmts_limit = []
                    for s in stmts:
                         stmts_limit.append(self.limit_stmt(limit_ref, s))
                    return Begin(stmts_limit, res_limit)
                case Closure(n, params):
                    return s
                case Call(Name('arity'), [exp]):
                    return s
                case Uninitialized(ty):
                    return s
                case Subscript(tup, index, Load()):
                    t_s = self.limit_exp(limit_ref, tup)
                    n_s = self.limit_exp(limit_ref, index)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.limit_exp(limit_ref, tup)
                    return Call(Name('len'), [t_s])
                case FunRef(id, arity):
                    return s
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case Call(func, args):
                    shrink_fun = self.limit_exp(limit_ref, func)
                    shrink_args = []
                    if len(args) > 6:
                         for i in range(5):
                              shrink_args.append(self.limit_exp(limit_ref, args[i]))
                         limit_args = []
                         for i in range(5, len(args)):
                              limit_args.append(self.limit_exp(limit_ref, args[i])) # pack args to Tuple 
                         shrink_args.append(Tuple(limit_args, Load()))
                    else:
                         for ag in args:
                              shrink_args.append(self.limit_exp(limit_ref, ag))
                    return Call(shrink_fun, shrink_args)
                case _ :
                    raise Exception('error in limit exp, unexpected ' + repr(s)) 
         
    def limit_stmt(self, limited_ref:list, s: stmt) -> stmt:
        match s:
            case If(test, body, orelse):
                res = self.limit_exp(limited_ref,test)
                body_exp = []
                for b in body:
                     body_exp.append(self.limit_stmt(limited_ref, b))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.limit_stmt(limited_ref, o))
                return If(res, body_exp, or_exp)
            case Expr(Call(Name('print'), [arg])):
                val = self.limit_exp(limited_ref, arg)
                return Expr(Call(Name('print'), [val]))
            case Expr(value):
                val = self.limit_exp(limited_ref, value)
                return Expr(val)
            case Assign([Name(id)], value):
                val = self.limit_exp(limited_ref, value)
                return Assign([Name(id)], val)
            case While(exp, stmts, []):
                  cond_shrink = self.limit_exp(limited_ref, exp)
                  stmts_shrink = []
                  for x in stmts:
                    stmts_shrink.append(self.limit_stmt(limited_ref, x))
                  return While(cond_shrink, stmts_shrink, [])
            case Collect(size):
                    return s
            case Return(e):
                    return Return(self.limit_exp(limited_ref, e))
            case Assign([Subscript(tup, index, Store())], value):
                    tup_s = self.limit_exp(limited_ref, tup)
                    index_s = self.limit_exp(limited_ref, index)
                    val_s = self.limit_exp(limited_ref, value)
                    return Assign([Subscript(tup_s, index_s, Store())], val_s)
            case _:
                return self.limit_exp(limited_ref, s)
    
    def limit_functions(self, p):
            match p:
                case Module(body):
                    functions = [] 
                    for x in body:
                        match x:
                             case FunctionDef(name, params, bod, dl, returns, comment):
                                  limited_ref = []
                                  if len(params) > 6:
                                        args = []
                                        for i in range(5):
                                             args.append(params[i]) # consider first 5 args
                                        types_tuple = []
                                        for i in range(5,len(params)):
                                             types_tuple.append(params[i][1]) # assuming its a tuple of type(var, type)
                                             limited_ref.append(params[i][0])
                                        added_arg = ('tup', TupleType(types_tuple))
                                        args.append(added_arg)
                                        params = args
                                  limit_stmts = []
                                  for b in bod:
                                        limit_stmts.append(self.limit_stmt(limited_ref, b))
                                  functions.append(FunctionDef(name, params, limit_stmts, dl, returns, comment))
                    return Module(functions)
                case _ :
                    raise Exception('error in limit main module, unexpected ' + repr(p))


    ############################################################################
    # Expose Allocation
    ############################################################################ 

    def expose_alloc_exp(self, e: expr) -> expr:
            match e:
                case BinOp(left, Add(), right):
                    l = self.expose_alloc_exp(left)
                    r = self.expose_alloc_exp(right)
                    return BinOp(l, Add(), r)
                case BinOp(left, Sub(), right):
                    l = self.expose_alloc_exp(left)
                    r = self.expose_alloc_exp(right)
                    return BinOp(l, Sub(), r)
                case UnaryOp(USub(), v):
                    val = self.expose_alloc_exp(v)
                    return UnaryOp(USub(), val)
                case IfExp(test, body, orelse):
                    test_exp = self.expose_alloc_exp(test)
                    body_exp = self.expose_alloc_exp(body)
                    or_exp = self.expose_alloc_exp(orelse)
                    return IfExp(test_exp, body_exp, or_exp)
                case UnaryOp(Not(), v):
                    val = self.expose_alloc_exp(v)
                    return UnaryOp(Not(), val)
                case Compare(left, [cmp], [right]):
                    l = self.expose_alloc_exp(left)
                    r = self.expose_alloc_exp(right)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return e
                case Call(Name('input_int'), []):
                      return e
                case Name(id):
                    return e
                case Uninitialized(ty):
                      return e
                case Begin(stmts, res):
                      res_expose = self.expose_alloc_exp(res)
                      stmt_exp = []
                      for ss in stmts:
                           tmp = self.expose_alloc_stmt(ss)
                           for y in tmp:
                                stmt_exp.append(y)
                      return Begin(stmt_exp, res_expose)
                case Call(Name('arity'), [exp]):
                      e_s = self.expose_alloc_exp(exp)
                      return Call(Name('arity'), [e_s])
                case Tuple(es, Load()):
                    # use a list for mutability
                    begin_stms = []
                    t_len = 0
                    temp_var = []
                    for s in es:
                         t_len = t_len + 1
                         exp_e = self.expose_alloc_exp(s)
                         if type(exp_e) == Uninitialized: # we don't need to initialize unint value types
                              continue
                         var = generate_name("init")
                         temp_var.append(var)
                         begin_stms.append(Assign([Name(var)],exp_e))
                    bytes_req = 8 + t_len * 8
                    begin_stms.append(If(Compare(BinOp(self.free_ptr,Add(),Constant(bytes_req)),[Lt()],[self.fromspace_end]), [], [Collect(bytes_req)]))
                    tuple = generate_name('alloc')
                    begin_stms.append(Assign([Name(tuple)],Allocate(t_len, e.has_type)))
                    for ind in range(len(temp_var)):
                         begin_stms.append(Assign([Subscript(Name(tuple), Constant(ind), Store())], Name(temp_var[ind])))
                    return Begin(begin_stms, Name(tuple))
                case Closure(n, es):
                    begin_stms = []
                    t_len = 0
                    temp_var = []
                    for s in es:
                         t_len = t_len + 1
                         exp_e = self.expose_alloc_exp(s)
                         var = generate_name("init")
                         temp_var.append(var)
                         begin_stms.append(Assign([Name(var)],exp_e))
                    bytes_req = 8 + t_len * 8
                    begin_stms.append(If(Compare(BinOp(self.free_ptr,Add(),Constant(bytes_req)),[Lt()],[self.fromspace_end]), [], [Collect(bytes_req)]))
                    tuple = generate_name('alloc')
                    begin_stms.append(Assign([Name(tuple)],AllocateClosure(t_len, e.has_type, n)))
                    print("Type of has Type var of closure-", type(e.has_type))
                    for ind in range(len(temp_var)):
                         begin_stms.append(Assign([Subscript(Name(tuple), Constant(ind), Store())], Name(temp_var[ind])))
                    return Begin(begin_stms, Name(tuple))
                case Subscript(tup, index, Load()):
                    tup_rco = self.expose_alloc_exp(tup)
                    ind_rco = self.expose_alloc_exp(index)
                    return Subscript(tup_rco, ind_rco, Load())
                case Call(Name('len'), [tup]):
                    tup_rco = self.expose_alloc_exp(tup)
                    return Call(Name('len'), [tup_rco])
                case Call(func, args):
                      fun_rco = self.expose_alloc_exp(func)
                      args_rco = []
                      for a in args:
                           args_rco.append(self.expose_alloc_exp(a))
                      return Call(fun_rco, args_rco)
                case FunRef(id, arity):
                    return e
                case Allocate(length, typ):
                    return e
                case GlobalValue(name):
                    return e
                case _:
                    raise Exception('error in expose_alloc_exp, unexpected ' + repr(e))

    def expose_alloc_stmt(self, s: stmt) -> List[stmt]:
        res = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                val = self.expose_alloc_exp(arg)
                print_stmt = Expr(Call(Name('print'), [val])) 
                res.append(print_stmt)
            case Expr(value):
                val = self.expose_alloc_exp(value)
                res.append(val)
            case Assign([Name(id)], value):
                val = self.expose_alloc_exp(value)
                res.append(Assign([Name(id)], val))
            case If(test, body, orelse):
                val = self.expose_alloc_exp(test)
                body_exp = []
                for b in body:
                     v = self.expose_alloc_stmt(b)
                     for v1 in v:
                        body_exp.append(v1)
                or_exp = []
                for o in orelse:
                     v = self.expose_alloc_stmt(o)
                     for v1 in v:
                        or_exp.append(v1)
                res.append(If(val, body_exp, or_exp)) 
            case While(test, stmts, []):
                  test_con = self.expose_alloc_exp(test)
                  exp_stmts = []
                  for x in stmts:
                       res_stmts = self.expose_alloc_stmt(x)
                       for y in res_stmts:
                            exp_stmts.append(y)
                  res.append(While(test_con, exp_stmts, []))
            case Collect(size):
                  return s
            case Assign([Subscript(tup, index, Store())], value):
                  t_atm = self.expose_alloc_exp(tup)
                  i_atm = self.expose_alloc_exp(index)
                  val_atm = self.expose_alloc_exp(value)
                  res.append(Assign([Subscript(t_atm, i_atm, Store())], val_atm))
            case Return(e):
                    res.append(Return(self.expose_alloc_exp(e)))
            case FunctionDef(name, params, bod, dl, returns, comment):
                    limit_stmts = []
                    for b in bod:
                         exp_stmts = self.expose_alloc_stmt(b)
                         for ex in exp_stmts:
                              limit_stmts.append(ex)
                    res.append(FunctionDef(name, params, limit_stmts, dl, returns, comment))
            case _:
                raise Exception('error in expose_alloc_stmt, unexpected ' + repr(s))
        
        return res
    
    def expose_allocation(self, p: Module) -> Module:
        match p:
            case Module(body):
                 res = [] 
                 for x in body:
                    res_Stmt = self.expose_alloc_stmt(x)
                    for y in res_Stmt:
                         res.append(y)
                 return Module(res)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))


    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> TupleTyping[expr, Temporaries]:
            match e:
                case BinOp(left, Add(), right):
                    temp = []
                    l = self.rco_exp(left, True)
                    for x in l[1]:
                         temp.append(x)
                    r = self.rco_exp(right, True)
                    for x in r[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), BinOp(l[0] , Add(), r[0])))
                         return (Name(var), temp)
                    else:
                         return (BinOp(l[0], Add(), r[0]),temp)
                case BinOp(left, Sub(), right):
                    l = self.rco_exp(left, True)
                    r = self.rco_exp(right, True)
                    temp = []
                    for x in l[1]:
                         temp.append(x)
                    for x in r[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var),BinOp(l[0] , Sub(), r[0])))
                         return (Name(var), temp)
                    else:
                         return (BinOp(l[0], Sub(), r[0]),temp)
                case UnaryOp(USub(), v):
                    val = self.rco_exp(v, True)
                    temp = []
                    for x in val[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), UnaryOp(USub(), val[0])))
                         return (Name(var), temp)
                    else:
                         return (UnaryOp(USub(), val[0]),temp)
                case IfExp(test, body, orelse):
                    test_exp = self.rco_exp(test, True)
                    body_exp = self.rco_exp(body, False)
                    or_exp = self.rco_exp(orelse, False)
                    temp = []; body_b = None; or_b = None; body_stmts = []; or_stmts = []
                    for x in test_exp[1]:
                         temp.append(x)
                    for x in body_exp[1]:
                         body_stmts.append(Assign([x[0]],x[1]))
                    body_b = Begin(body_stmts, body_exp[0])
                    for x in or_exp[1]:
                         or_stmts.append(Assign([x[0]],x[1]))
                    or_b = Begin(or_stmts, or_exp[0])
                    if body_b == None:
                              body_b = body_exp[0]
                    if or_b == None:
                              or_b = or_exp[0]
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), IfExp(test_exp[0], body_b, or_b)))
                         return (Name(var), temp)
                    else:
                         return (IfExp(test_exp[0], body_b, or_b), temp)
                case UnaryOp(Not(), v):
                    val = self.rco_exp(v, True)
                    temp = []
                    for x in val[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), UnaryOp(Not(), val[0])))
                         return (Name(var), temp)
                    else:
                         return (UnaryOp(Not(), val[0]),temp)
                case Compare(left, [cmp], [right]):
                    l = self.rco_exp(left, True)
                    r = []
                    temp = []
                    for x in l[1]:
                         temp.append(x)
                    r = self.rco_exp(right, True)
                    for x in r[1]:
                         temp.append(x)
                    return (Compare(l[0], [cmp], [r[0]]), temp)
                case Constant(value):
                    return (e, [])
                case Call(Name('input_int'), []):
                    var = generate_name("temp")
                    temp = [(Name(var), Call(Name('input_int'), []))]
                    return (Name(var), temp)
                case Name(id):
                    return (e, [])
                case Begin(stmts, res):
                    res_rco = self.rco_exp(res, True)
                    temp = []
                    rco_stmts = []
                    for s in stmts:
                         stmts = self.rco_stmt(s)
                         for ss in stmts:
                              rco_stmts.append(ss)
                    for x in res_rco[1]:
                         rco_stmts.append(Assign([x[0]],x[1]))
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var),Begin(rco_stmts, res_rco[0])))
                         return (Name(var), temp)
                    else:
                         return (Begin(rco_stmts, res_rco[0]),temp)                      
                case Subscript(tup, index, Load()):
                    tup_rco = self.rco_exp(tup, True)
                    temp = []
                    for x in tup_rco[1]:
                         temp.append(x)
                    ind_rco = self.rco_exp(index, True)
                    for x in ind_rco[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), Subscript(tup_rco[0], ind_rco[0], Load())))
                         return (Name(var), temp)
                    else:
                         return (Subscript(tup_rco[0], ind_rco[0], Load()), temp)
                case Call(Name('len'), [tup]):
                    tup_rco = self.rco_exp(tup, True)
                    temp = []
                    for x in tup_rco[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), Call(Name('len'), [tup_rco[0]])))
                         return (Name(var), temp)
                    else:
                         return (Call(Name('len'), [tup_rco[0]]),temp)
                case Call(Name('arity'), [exp]):
                    tup_rco = self.rco_exp(tup, True)
                    temp = []
                    for x in tup_rco[1]:
                         temp.append(x)
                    if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), Call(Name('arity'), [tup_rco[0]])))
                         return (Name(var), temp)
                    else:
                         return (Call(Name('arity'), [tup_rco[0]]),temp)
                case Allocate(length, typ):
                    return (Allocate(length, typ),[])
                case AllocateClosure(length, typ, arity):
                      return (AllocateClosure(length, typ, arity), [])
                case Uninitialized(ty):
                    return (Uninitialized(ty), [])
                case Call(func, args):
                      print("rco of call statement - ", [e])
                      fun_rco = self.rco_exp(func, True)
                      args_rco = []
                      temp = []
                      for x in fun_rco[1]:
                           temp.append(x)
                      for a in args:
                           arg_rco = self.rco_exp(a, True)
                           for i in arg_rco[1]:
                                temp.append(i)
                           args_rco.append(arg_rco[0])
                      if need_atomic:
                         var = generate_name("temp")
                         temp.append((Name(var), Call(fun_rco[0], args_rco)))
                         return (Name(var), temp)
                      else:
                         return (Call(fun_rco[0], args_rco), temp)
                case FunRef(id, arity):
                    temp = []
                    if need_atomic:
                         fun_var = generate_name("func")
                         temp.append((Name(fun_var), e))
                         return (Name(fun_var), temp)
                    else:
                         return (e, temp)
                case GlobalValue(name):
                    return (e,[])
                case _:
                    raise Exception('error in rco_exp, unexpected ' + repr(e))

    def rco_stmt(self, s: stmt) -> List[stmt]:
        res = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                val = self.rco_exp(arg, True)
                for x in val[1]:
                    res.append(Assign([x[0]],x[1]))
                print_stmt = Expr(Call(Name('print'), [val[0]])) 
                res.append(print_stmt)
            case Expr(value):
                val = self.rco_exp(value, True)
                for x in val[1]:
                    res.append(Assign([x[0]],x[1]))
            case Assign([Name(id)], value):
                val = self.rco_exp(value, True)
                for x in val[1]:
                    res.append(Assign([x[0]],x[1]))
                res.append(Assign([Name(id)], val[0]))
            case If(test, body, orelse):
                val = self.rco_exp(test, True)
                for x in val[1]:
                    res.append(Assign([x[0]],x[1]))
                body_exp = []
                for b in body:
                     v = self.rco_stmt(b)
                     for v1 in v:
                        body_exp.append(v1)
                or_exp = []
                for o in orelse:
                     v = self.rco_stmt(o)
                     for v1 in v:
                        or_exp.append(v1)
                res.append(If(val[0], body_exp, or_exp)) 
            case While(test, stmts, []):
                  test_con = self.rco_exp(test, False)
                  test_stmts = []
                  if len(test_con[1]) > 0:
                       for x in test_con[1]:
                         test_stmts.append(Assign([x[0]],x[1]))
                       test_b = Begin(test_stmts, test_con[0])
                  else:
                       test_b = test_con[0]
                  rco_stmts = []
                  for x in stmts:
                       v = self.rco_stmt(x)
                       if type(v) == TupleType: #res from rco_expr
                            for v1 in v[1]:
                                 rco_stmts.append(Assign([v1[0]],v1[1]))
                       elif type(v) == list:
                         for v1 in v:
                              rco_stmts.append(v1)
                  res.append(While(test_b, rco_stmts, []))
            case Collect(size):
                  res.append(s)
            case Assign([Subscript(tup, index, Store())], value):
                  t_atm = self.rco_exp(tup, True)
                  for i in t_atm[1]:
                       res.append(Assign([i[0]],i[1]))
                  i_atm = self.rco_exp(index, True)
                  for i in i_atm[1]:
                       res.append(Assign([i[0]],i[1]))
                  val_atm = self.rco_exp(value, True)
                  for i in val_atm[1]:
                       res.append(Assign([i[0]],i[1]))
                  res.append(Assign([Subscript(t_atm[0], i_atm[0], Store())], val_atm[0]))
            case Return(e):
                    res_atm = self.rco_exp(e, False)
                    for v1 in res_atm[1]:
                         res.append(Assign([v1[0]],v1[1]))
                    res.append(Return(res_atm[0]))
            case FunctionDef(name, params, bod, dl, returns, comment):
                    rco_stmts = []
                    for b in bod:
                         v = self.rco_stmt(b)
                         if type(v) == TupleType: #res from rco_expr
                            for v1 in v[1]:
                                 rco_stmts.append(Assign([v1[0]],v1[1]))
                         elif type(v) == list:
                            for v1 in v:
                                 rco_stmts.append(v1)
                    res.append(FunctionDef(name, params, rco_stmts, dl, returns, comment))
            case _:
                return self.rco_exp(s, True)
        
        return res
    
    def interp_stmt(self, s, cont, stmts: List[stmt]) -> List[stmt]:
        res = self.rco_stmt(s)
        for x in res:
            stmts.append(x)
        return self.interp_stmts(cont, stmts)
    
    def interp_stmts(self, ss, stmts: List[stmt]) -> List[stmt]:
        match ss:
            case []:
                return stmts
            case [s, *ss]:
                return self.interp_stmt(s, ss, stmts)


    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(body):
                pe_module = self.pe_P(p)
                res = self.interp_stmts(pe_module.body, [])
                return Module(res)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))
        
    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, body, basic_blocks, name="block", create_new = True):
         if create_new:
              label = generate_name(name)
         else:
              label = name
         basic_blocks[label_name(label)] = body
         return [Goto(label)], basic_blocks
    
    def explicate_effect(self, e: expr, cont, basic_blocks):
         match e:
              case IfExp(test, body, orelse):
                   # cont_block = create_block for the cont statements  - turns out bad if cont is a large list of statements.
                   cont_b = self.create_block(cont, basic_blocks)
                   body_b = self.explicate_effect(body, cont_b, basic_blocks)
                   or_b = self.explicate_effect(orelse, cont_b, basic_blocks)
                   ifexp = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return ifexp
              case Call(func, args):
                   stmts = [Expr(e)] + cont
                   return stmts
              case Begin(body, res):
                   cont_b = self.explicate_effect(res, cont, basic_blocks)
                   for s in reversed(body):
                    cont_b = self.explicate_stmt(s, cont_b, basic_blocks)
                   return cont_b
              case _:
                   return [e] + cont
              
    def explicate_assign(self, rhs, lhs, cont, basic_blocks):
         match rhs:
              case IfExp(test, body, orelse):
                   goto_cont, basic_blocks = self.create_block(cont, basic_blocks)
                   body_as = self.explicate_assign(body, lhs, goto_cont, basic_blocks)
                   or_as = self.explicate_assign(orelse, lhs, goto_cont, basic_blocks)
                   ifexp = self.explicate_pre(test, body_as, or_as, basic_blocks)
                   return ifexp
              case Begin(body, res):
                   cont_b = self.explicate_assign(res, lhs, cont, basic_blocks)
                   for s in reversed(body):
                         cont_b = self.explicate_stmt(s, cont_b, basic_blocks)
                   return cont_b
              case _:
                   return [Assign([lhs], rhs)] + cont
              
    def explicate_pre(self, cnd, thn, els, basic_blocks):
         match cnd:
              case Compare(left, [cmp], [right]):
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   return [If(cnd, goto_thn, goto_els)]
              case Constant(True):
                   return thn
              case Constant(False):
                   return els
              case UnaryOp(Not(), op):
                   test_exp = self.explicate_pre(op, els, thn, basic_blocks)
                   return test_exp
              case IfExp(test, body, orelse):
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   body_b = self.explicate_pre(body, goto_thn, goto_els, basic_blocks)
                   or_b = self.explicate_pre(orelse, goto_thn, goto_els, basic_blocks)
                   test_b = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return test_b
              case Begin(body, result):
                   cont_b = self.explicate_pre(result, thn, els, basic_blocks)
                   for s in reversed(body):
                         cont_b = self.explicate_stmt(s, cont_b, basic_blocks)
                   return cont_b
              case Name(id) :
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   return [If(Compare(cnd, [Eq()], [Constant(False)]), goto_els , goto_thn )]
              case Subscript(tup, index, Load()):
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   return [If(Compare(cnd, [Eq()], [Constant(False)]), goto_els , goto_thn )]
              case Call(func, args):
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   return [If(Compare(cnd, [Eq()], [Constant(False)]), goto_els , goto_thn )]
              case _:
                   raise Exception('error in explicate_pre, unexpected condition- ' + repr(cnd))
              
    def explicate_tail(self, basic_blocks, e: expr):
         match e:
              case IfExp(test, body, orelse):
                   exp_body = self.explicate_tail(basic_blocks, body)
                   exp_orelse = self.explicate_tail(basic_blocks, orelse)
                   return self.explicate_pre(test, exp_body, exp_orelse, basic_blocks)
              case Begin(body, res):
                   cont_b = self.explicate_tail(basic_blocks, res)
                   for s in reversed(body):
                    cont_b = self.explicate_stmt(s, cont_b, basic_blocks)
                   return cont_b
              case Call(func, args):
                   return [TailCall(func, args)]
              case _:
                   return [Return(e)]
         

    def explicate_stmt(self, s, cont, basic_blocks):
         match s:
              case Assign([lhs], rhs):
                   return self.explicate_assign(rhs, lhs, cont, basic_blocks)
              case Expr(Call(Name('print'), [arg])):
                    val = self.explicate_stmt(arg, cont, basic_blocks) #not required.
                    print_stmt = Expr(Call(Name('print'), [val[0]]))
                    return [print_stmt] + cont
              case Expr(value):
                   return self.explicate_effect(value, cont, basic_blocks)
              case If(test, body, orelse):
                   cont_goto, basic_blocks = self.create_block(cont, basic_blocks)
                   body_b = cont_goto
                   for s1 in reversed(body):
                        body_b = self.explicate_stmt(s1, body_b, basic_blocks)
                   or_b = cont_goto
                   for s1 in reversed(orelse):
                        or_b = self.explicate_stmt(s1, or_b, basic_blocks)
                   test_b = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return test_b
              case While(test, stmts, []):
                   cont_goto, basic_blocks = self.create_block(cont, basic_blocks)
                   label = generate_name("block")
                   body_b = [Goto(label)]
                   for s1 in reversed(stmts):
                        body_b = self.explicate_stmt(s1, body_b, basic_blocks)
                   while_b = self.explicate_pre(test, body_b, cont_goto, basic_blocks)
                   if_block, basic_blocks = self.create_block(while_b, basic_blocks, label, False)
                   return if_block
              case Return(e):
                   return self.explicate_tail(basic_blocks, e) 
              case _:
                   return [s] + cont
           
    def explicate_functions(self, s: stmt):
         match s:
              case FunctionDef(name, params, bod, dl, returns, comment):
                   fun_body = []
                   basic_blocks = {}
                   for ss in reversed(bod):
                        fun_body = self.explicate_stmt(ss, fun_body, basic_blocks)
                   basic_blocks[label_name(name+"_start")] = fun_body #prepending function name to start block of function
                   return FunctionDef(name, params, basic_blocks, None, returns, None)
              
    def explicate_control(self, p):
         match p:
              case Module(body):
                   new_body = [] # return is already defined in shrink pass
                   for b in body:
                         new_body.append(self.explicate_functions(b))
                   return CProgramDefs(new_body)
              case _:
                   raise Exception('error in explicate control, unexpected ' + repr(p))                   

    ############################################################################
    # Select Instructions
    ############################################################################

    def cmp_instr(self, cmp):
        match cmp:
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'

    def select_arg(self, e: expr) -> arg:
            match e:
                case Constant(value):
                    if value == True:
                        return Immediate(1)
                    elif value == False:
                         return Immediate(0)
                    else:
                        return Immediate(value)
                case Name(id):
                    return Variable(id)
                case Reg(id):
                    return Reg(id)
                case GlobalValue(name):
                      return self.getGlobal(name)
                case FunRef(id, arity):
                      return self.getGlobal(id)
                case _:
                    raise Exception('error in select_arg, unexpected ' + repr(e))   

    def select_exp(self, e: expr) -> List[instr]:
         res = []
         match e:
            case BinOp(left, Add(), right):
                l = self.select_arg(left)
                r = self.select_arg(right)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('addq', [r, Reg("rax")]))
                var = Reg('rax')
            case BinOp(left, Sub(), right):
                l = self.select_arg(left)
                r = self.select_arg(right)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('subq', [r, Reg("rax")]))
                var = Reg('rax')
            case UnaryOp(USub(), v):
                val = self.select_arg(v)
                neg_stmt = Instr('negq', [val])
                res.append(neg_stmt)
                var = val
            case UnaryOp(Not(), op):
                  val = self.select_arg(op)
                  xor_stmt = Instr('xorq', [Immediate(1), val])
                  res.append(xor_stmt)
                  var = op
            case Call(Name('input_int'), []):
                call_stmt = Callq("read_int",0)
                res.append(call_stmt)
                var = Reg('rax')
            case Compare(left, [cmp], [right]):
                    l = self.select_exp(left)
                    r = self.select_exp(right)
                    for x in l[1]:
                         res.append(x)
                    for x in r[1]:
                         res.append(x)
                    if type(r[0]) == Reg:
                        cmp_stmt = Instr('cmpq', [l[0], r[0]])
                    else:
                         cmp_stmt = Instr('cmpq', [r[0], l[0]])
                    res.append(cmp_stmt)
            case Subscript(tup, index, Load()):
                  tup_arg = self.select_arg(tup)
                  res.append(Instr('movq', [tup_arg, Reg('r11')]))
                  ind_loc = 8*(index.value+1)
                  var = Deref('r11',ind_loc)
                  return var,res
            case Call(Name('len'), [tup]):
                   tup_arg = self.select_arg(tup)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(1), Reg('rax')]))
                   var = Reg('rax')
                   return var,res
            case Call(Name('arity'), [exp]):
                   tup_arg = self.select_arg(exp)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(57), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(31), Reg('rax')]))
                   var = Reg('rax')
                   return var,res
            case Call(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x[1]) == Tuple:
                              for y in x[1]:
                                   arg_count = arg_count + 1 
                   res.append(IndirectCallq(func, arg_count)) 
                   var = Reg('rax')
                   return var,res
            case Allocate(length, typ):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Final Tag-", '{0:64b}'.format(tag) )
                   print(" obtained Tag for inst-",e," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   res.append(Instr('movq', [Reg('r11'), id]))
                   var = Reg('r11')
                   return var, res
            case AllocateClosure(length, typ, arity):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Initial Tag-", '{0:64b}'.format(tag) )
                   complete_tag = int((arity << 58) | tag)
                   print("arity Tag-", '{0:5b}'.format(arity) )
                   print(" obtained Tag for inst-",e," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   res.append(Instr('movq', [Reg('r11'), id]))
                   var = Reg('r11')
                   return var, res
            case _:
                var = self.select_arg(e)
         return var,res
                   

    def select_stmt(self, s: stmt, fun_name: str) -> List[instr]:
        res = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                val = self.handle_print(arg)
                inst_stmt = Instr('movq', [val[1], Reg("rdi")])
                call_stmt = Callq("print_int", 0)
                for x in val[0]:
                     res.append(x)
                res.append(inst_stmt)
                res.append(call_stmt)
            case Expr(exp):
                r = self.select_exp(exp)
                for x in r[1]:
                    res.append(x)
            case Assign([Name(id)], value):
                assign_stmt = self.handle_assign(value, Variable(id))
                for x in assign_stmt[1]:
                    res.append(x)
            case If(Compare(left, [cmp], [right]), [Goto(iflabel)], [Goto(elselabel)]):
                left_arg = self.select_exp(left)
                right_arg = self.select_exp(right)
                for x in left_arg[1]:
                     res.append(x)
                for x in right_arg[1]:
                     res.append(x)
                cmp_stmt = Instr('cmpq', [right_arg[0], left_arg[0]])
                cmp_op = self.cmp_instr(cmp)
                jmp_if = JumpIf(cmp_op, iflabel)
                jmp_else = Jump(elselabel)
                res.append(cmp_stmt)
                res.append(jmp_if)
                res.append(jmp_else) 
            case Goto(label):
                  jmp_inst = Jump(label)
                  res.append(jmp_inst)
            case Return(val):
                  v = self.select_exp(val)
                  for x in v[1]:
                       res.append(x)
                  mov_inst = Instr('movq', [v[0], Reg('rax')])
                  jmp_inst = Jump(fun_name+'_conclusion') # generate inst with function name included
                  res.append(mov_inst)
                  res.append(jmp_inst)
            case TailCall(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x[1]) == Tuple:
                              for y in x[1]:
                                   arg_count = arg_count + 1 
                   func_exp = self.select_arg(func)
                   res.append(TailJump(func_exp, arg_count))
            case Assign([Subscript(tup, index, Store())], value):
                  res.append(Instr('movq', [self.select_arg(tup), Reg('r11')]))
                  ind_loc = 8*(index.value+1)
                  val = self.select_arg(value)
                  if type(value) == FunRef:
                        inst_stmt = Instr('leaq', [val, Reg("rip")]) # how to define the assignment ? 
                  else:
                       inst_stmt = Instr('movq', [val, Deref('r11',ind_loc)])
                  res.append(inst_stmt)
            case Collect(size):
                  res.append(Instr('movq', [Reg('r15'), Reg('rdi')]))
                  res.append(Instr('movq', [Immediate(size), Reg('rsi')]))
                  res.append(Callq("collect", 0))
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))  
            
        return res
    

    # The s param was stmt before !!
    def handle_assign(self, s: expr, id: any):
         res = [] 
         match s:
            case Call(Name('print'), [arg]):
                res = []
            case BinOp(left, Add(), right):
                l,inst_l = self.handle_assign(left,None)
                r,inst_r = self.handle_assign(right,None)
                for x in inst_l:
                     res.append(x)
                if id == l:
                    for y in inst_r:
                      res.append(y)
                    res.append(Instr('addq', [l, r]))
                elif  id == r:
                    for y in inst_r:
                      res.append(y)
                    res.append(Instr('addq', [r, l]))
                else:
                    res.append(Instr('movq', [l, id]))
                    for y in inst_r:
                     res.append(y)
                    res.append(Instr('addq', [r, id]))
                return id,res
            case BinOp(left, Sub(), right):
                    l,inst_l = self.handle_assign(left,None)
                    r,inst_r = self.handle_assign(right,None)
                    for x in inst_l:
                     res.append(x)
                    for y in inst_r:
                     res.append(y)
                    if id == l:
                        res.append(Instr('subq', [l, r]))
                    elif  id == r:
                        res.append(Instr('subq', [r, l]))
                    else:
                        res.append(Instr('movq', [l, id]))
                        res.append(Instr('subq', [r, id]))
                    return id,res
            case UnaryOp(USub(), v):
                    val,inst = self.handle_assign(v,None)
                    for x in inst:
                     res.append(x)
                    neg_stmt = Instr('negq', [id])
                    res.append(Instr('movq', [val, id]))
                    res.append(neg_stmt)
                    return id, res
            case UnaryOp(Not(), op):
                    if op != id:
                        val,inst = self.handle_assign(op,None)
                        for x in inst:
                            res.append(x)
                    xor_stmt = Instr('xorq', [Immediate(1), id])
                    res.append(xor_stmt)
                    return id, res
            case Call(Name('input_int'), []):
                    inst_stmt = Instr('movq', [Reg("rax"),id])
                    call_stmt = Callq("read_int",0)
                    res.append(call_stmt)
                    if id != None:
                         res.append(inst_stmt)
                    return Reg("rax"),res
            case Compare(left, [cmp], [right]):
                   left_arg = self.handle_assign(left, None)
                   right_arg = self.handle_assign(right, None)
                   for x in left_arg[1]:
                        res.append(x)
                   for x in right_arg[1]:
                        res.append(x)
                   cmp_stmt = Instr('cmpq', [right_arg[0], left_arg[0]])
                   cmp_op = self.cmp_instr(cmp)
                   set_inst = Instr('set'+cmp_op, [Reg("al")])
                   mov_inst = Instr('movzbq',[Reg("al"), id])
                   res.append(cmp_stmt)
                   res.append(set_inst)
                   res.append(mov_inst)
                   return id, res
            case If(Compare(left, [cmp], [right]), [Goto(iflabel)], [Goto(elselabel)]):
                    left_arg = self.handle_assign(left, None)
                    right_arg = self.handle_assign(right, None)
                    for x in left_arg[1]:
                        res.append(x)
                    for x in right_arg[1]:
                        res.append(x)
                    cmp_stmt = Instr('cmpq', [right_arg[0], left_arg[0]])
                    cmp_op = self.cmp_instr(cmp)
                    jmp_if = JumpIf(cmp_op, iflabel)
                    jmp_else = Jump(elselabel)
                    res.append(cmp_stmt)
                    res.append(jmp_if)
                    res.append(jmp_else) 
            case Subscript(tup, index, Load()):
                  tup_arg = self.select_arg(tup)
                  res.append(Instr('movq', [tup_arg, Reg('r11')]))
                  ind_loc = 8*(index.value+1)
                  res.append(Instr('movq', [Deref('r11',ind_loc), id]))
                  return id,res
            case Call(Name('len'), [tup]):
                   tup_arg = self.select_arg(tup)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(1), Reg('rax')]))
                   res.append(Instr('movq', [Reg('rax'), id]))
                   return id,res
            case Allocate(length, typ):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Final Tag-", '{0:64b}'.format(tag) )
                   print(" obtained Tag for inst-",s," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   res.append(Instr('movq', [Reg('r11'), id]))
                   return id, res
            case AllocateClosure(length, typ, arity):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Initial Tag-", '{0:64b}'.format(tag) )
                   complete_tag = int((arity << 58) | tag)
                   print("arity Tag-", '{0:5b}'.format(arity) )
                   print(" obtained Tag for inst-",s," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   res.append(Instr('movq', [Reg('r11'), id]))
                   return id, res
            case Call(Name('arity'), [exp]):
                   tup_arg = self.select_arg(exp)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(57), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(31), Reg('rax')]))
                   res.append(Instr('movq', [Reg('rax'), id]))
                   return id,res
            case Call(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x) == Tuple:
                              for y in x:
                                   arg_count = arg_count + 1 
                   func_arg = self.select_arg(func)
                   res.append(IndirectCallq(func_arg, arg_count)) 
                   res.append(Instr('movq', [Reg('rax'), id]))
                   return id,res
            case TailCall(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x[1]) == Tuple:
                              for y in x[1]:
                                   arg_count = arg_count + 1 
                   func_exp = self.select_arg(func)
                   res.append(TailJump(func_exp, arg_count)) 
                   res.append(Instr('movq', [Reg('rax'), id])) # ideally an assignment cannot be a tail call !!!
                   return id,res
            case _:
                   arg = self.select_arg(s)
                   if type(s) == FunRef:
                        inst_stmt = Instr('leaq', [arg, id])
                   else:
                        inst_stmt = Instr('movq', [arg, id])
                   if id != None:
                    res.append(inst_stmt)
                   return arg,res

    def handle_print(self, s: expr):
         res = [] 
         match s:
            case Call(Name('print'), []):
                res = []
            case BinOp(left, Add(), right):
                inst_l,l = self.handle_print(left)
                inst_r,r = self.handle_print(right)
                for x in inst_l:
                     res.append(x)
                for x in inst_r:
                     res.append(x)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('addq', [r, Reg("rax")]))
                return res,Reg("rax")
            case BinOp(left, Sub(), right):
                inst_l,l = self.handle_print(left)
                inst_l,r = self.handle_print(right)
                for x in inst_l:
                     res.append(x)
                for x in inst_r:
                     res.append(x)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('subq', [r, Reg("rax")]))
                return res,Reg("rax")
            case UnaryOp(USub(), v):
                inst,val = self.handle_print(v)
                for x in inst:
                     res.append(x)
                res.append(Instr('movq', [val, Reg("rax")]))
                res.append(Instr('negq', Reg("rax")))
                return res,Reg("rax")
            case UnaryOp(Not(), v):
                inst,val = self.handle_print(v)
                for x in inst:
                     res.append(x)
                res.append(Instr('xorq', [Immediate(1), Reg("rax")]))
                return res,Reg("rax")
            case Call(Name('input_int'), []):
                call_stmt = Callq("read_int",0)
                res.append(call_stmt)
                return res,Reg("rax")
            case Compare(left, [cmp], [right]):
                   left_arg = self.handle_print(left)
                   right_arg = self.handle_print(right)
                   for x in left_arg[1]:
                        res.append(x)
                   for x in right_arg[1]:
                        res.append(x)
                   cmp_stmt = Instr('cmpq', [right_arg[0], left_arg[0]])
                   cmp_op = self.cmp_instr(cmp)
                   set_inst = Instr('set'+cmp_op, [Reg("al")])
                   mov_inst = Instr('movzbq',[Reg("al"), Reg("rax")])
                   res.append(cmp_stmt)
                   res.append(set_inst)
                   res.append(mov_inst)
                   return res, Reg("rax")
            case If(Compare(left, [cmp], [right]), [Goto(iflabel)], [Goto(elselabel)]):
                    left_arg = self.handle_print(left)
                    right_arg = self.handle_print(right)
                    for x in left_arg[1]:
                        res.append(x)
                    for x in right_arg[1]:
                        res.append(x)
                    cmp_stmt = Instr('cmpq', [right_arg[0], left_arg[0]])
                    cmp_op = self.cmp_instr(cmp)
                    jmp_if = JumpIf(cmp_op, iflabel)
                    jmp_else = Jump(elselabel)
                    res.append(cmp_stmt)
                    res.append(jmp_if)
                    res.append(jmp_else) 
            case Subscript(tup, index, Load()):
                  tup_arg = self.select_arg(tup)
                  res.append(Instr('movq', [tup_arg, Reg('r11')]))
                  ind_loc = 8*(index.value+1)
                  return res, Deref('r11',ind_loc)
            case Call(Name('len'), [tup]):
                   tup_arg = self.select_arg(tup)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(1), Reg('rax')]))
                   return res,Reg('rax')
            case Call(Name('arity'), [exp]):
                   tup_arg = self.select_arg(exp)
                   res.append(Instr('movq', [tup_arg, Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('movq', [Deref('rax',0), Reg('rax')]))
                   res.append(Instr('sarq', [Immediate(57), Reg('rax')])) 
                   res.append(Instr('andq', [Immediate(31), Reg('rax')]))
                   return res,Reg('rax')
            case Call(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x[1]) == Tuple:
                              for y in x[1]:
                                   arg_count = arg_count + 1 
                   func_arg = self.select_arg(func)
                   res.append(IndirectCallq(func_arg, arg_count)) 
                   return res,Reg('rax')
            case TailCall(func, args):
                   arg_count = 0
                   for ind, x in enumerate(args):
                         l = self.select_exp(x)
                         for j in l[1]:
                              res.append(j)
                         res.append(Instr('movq', [l[0], self.arg_regs[ind]])) # move args to arg passing register
                         if ind != 5 :
                              arg_count = arg_count + 1
                         elif ind == 5 and type(x[1]) == Tuple:
                              for y in x[1]:
                                   arg_count = arg_count + 1 
                   func_exp = self.select_arg(func)
                   res.append(TailJump(func_exp, arg_count)) 
                   return res,Reg('rax')
            case Allocate(length, typ):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Final Tag-", '{0:64b}'.format(tag) )
                   print(" obtained Tag for inst-",s," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   return res, Reg('r11')
            case AllocateClosure(length, typ, arity):
                   tag = []
                   if type(typ) == TupleType:
                        types = typ.types
                        for i in range(length):
                             if type(types[i]) == TupleType:
                                  tag.append('1')
                             else:
                                  tag.append('0')
                   tag.reverse()
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   print("Generated TAG-", tag)
                   bin_tag= int(tag, 2)
                   tag = int((bin_tag << 1) | 1)
                   print("Initial Tag-", '{0:64b}'.format(tag) )
                   complete_tag = int((arity << 58) | tag)
                   print("arity Tag-", '{0:5b}'.format(arity) )
                   print(" obtained Tag for inst-",s," is-",tag)
                   res.append(Instr('movq', [self.getGlobal("free_ptr"), Reg('r11')]))
                   res.append(Instr('addq', [Immediate(8*(length+1)), self.getGlobal("free_ptr")]))
                   res.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                   return res, Reg('r11')
            case _:
                return res,self.select_arg(s) 
            
         return res
       

    def select_interp_stmt(self, s, cont, stmts: List[stmt], fun_name: str) -> List[instr]:
        res = self.select_stmt(s, fun_name)
        for x in res:
            stmts.append(x)
        return self.select_interp_stmts(cont, stmts, fun_name)
    
    def select_interp_stmts(self, ss, stmts: List[stmt], fun_name: str) -> List[instr]:
        match ss:
            case []:
                return stmts
            case [s, *ss]:
                return self.select_interp_stmt(s, ss, stmts, fun_name)    

    def select_instructions(self, p: Module) -> X86ProgramDefs:
         match p:
            case CProgramDefs(body):
                functions = []
                for x in body:
                    match x:
                         case FunctionDef(name, params, bod, dl, returns, comment):
                               blocks = {}
                               self.varTypes[name] = x.var_types
                               for (l, ss) in bod.items():
                                   add_instr = []
                                   if l == name+"_start":
                                        for ind,p in enumerate(params):
                                             add_instr.append(Instr('movq', [self.arg_regs[ind], Variable(p[0])])) # moving all args from registers to veriables
                                   l_stmt = []
                                   l_stmt = self.select_interp_stmts(ss, l_stmt, name)
                                   for inst in l_stmt:
                                        add_instr.append(inst)
                                   if len(add_instr) > 0: #work-around to avoid empty blockss.
                                        blocks[l] = add_instr
                               functions.append(FunctionDef(name, [], blocks, None, returns, None))
                         case _:
                              raise Exception('error in select_instructions, unexpected function ref' + repr(p)) 
                return X86ProgramDefs(functions)
            case _:
                raise Exception('error in select_instructions, unexpected ' + repr(p))      

    ############################################################################
    # Challenge 5.10
    ############################################################################

    def remove_unused_blocks(self, body, graph:DirectedAdjList):
         print(" In remove unused blocks - \n" )
         new_body = {}
         in_edges_blocks = {}
         for x in body:
              if x == 'conclusion':
                   continue
              in_edges = graph.ins[x]
              if len(in_edges) == 1:
                   in_edges_blocks[in_edges[0]] = x
         for x in in_edges_blocks.keys():
              for inst in body[x]:
                   if type(inst) == Jump and inst.label == in_edges_blocks[x]:
                        break
                   in_edges_blocks[x] = []
         for x in body:
              if x == 'conclusion':
                   continue
              if x in in_edges_blocks.values() and x not in in_edges_blocks.keys():
                   continue
              
              new_body[x] = []
              if x in in_edges_blocks.keys() and in_edges_blocks[x] == []:
                   
                   for inst in body[x]:
                        if type(inst) == Jump and inst.label == in_edges_blocks[x]:
                             if in_edges_blocks[x] in new_body.keys():
                                for add_inst in new_body[in_edges_blocks[x]]:
                                  new_body[x].append(add_inst)
                             else:
                                for add_inst in body[in_edges_blocks[x]]:
                                    new_body[x].append(add_inst)
                        else:
                             new_body[x].append(inst)
              else:
                for inst in body[x]:
                     new_body[x].append(inst)      
                   
         return new_body
                   
         
    ############################################################################
    # Assign Homes
    ############################################################################
         
    def assign_homes_arg(self, a: arg, reg_var: dict) -> arg:
        match a:
            case Immediate(value):
                return Immediate(value)
            case Variable(id):
                return reg_var[a]
            case Reg(id):
                return Reg(id)
            case Global(value):
                  return a
            case Deref(reg, off):
                  return a
            case _:
                raise Exception('error in assign_homes_arg, unexpected ' + repr(a))       

    def assign_homes_instr(self, i: instr,
                           reg_var: dict) -> instr:
     #    print("Register Variable DICT-", reg_var,"\n")
        match(i):
            case Instr('movq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('addq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('addq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('subq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('subq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('andq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('andq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('sarq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('sarq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('negq', [arg1]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    inst_stmt = Instr('negq', [arg1_stmt])
                    return inst_stmt
            case Instr('xorq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg2, reg_var)
                    inst_stmt = Instr('xorq', [arg1, arg1_stmt])
                    return inst_stmt
            case Callq("read_int",0):
                    return i
            case Callq("print_int", 0):
                    return i
            case Callq("collect", 0):
                    return i
            case Instr('cmpq', [arg1, arg2]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                   inst_stmt = Instr('cmpq', [arg1_stmt, arg2_stmt])
                   return inst_stmt
            case Instr('sete',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('sete', [arg1_stmt])
                   return inst_stmt
            case Instr('setne',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('setne', [arg1_stmt])
                   return inst_stmt 
            case Instr('setle',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('setle', [arg1_stmt])
                   return inst_stmt
            case Instr('setl',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('setl', [arg1_stmt])
                   return inst_stmt
            case Instr('setge',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('setge', [arg1_stmt])
                   return inst_stmt
            case Instr('setg',[arg1]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   inst_stmt = Instr('setg', [arg1_stmt])
                   return inst_stmt
            case Instr('movzbq', [arg1, arg2]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                   inst_stmt = Instr('movzbq', [arg1_stmt, arg2_stmt])
                   return inst_stmt
            case Instr('leaq', [arg1, arg2]):
                   arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                   arg2_stmt = self.assign_homes_arg(arg2, reg_var)
                   inst_stmt = Instr('leaq', [arg1_stmt, arg2_stmt])
                   return inst_stmt
            case IndirectCallq(func, arg_count):
                   arg1_stmt = self.assign_homes_arg(func, reg_var)
                   return IndirectCallq(arg1_stmt, arg_count)
            case TailJump(func, arg_count):
                   arg1_stmt = self.assign_homes_arg(func, reg_var)
                   return TailJump(arg1_stmt, arg_count)
            case Callq(func, airty):
                   arg1_stmt = self.assign_homes_arg(func, reg_var)
                   return Callq(arg1_stmt, airty)
            case Jump(label):
                   return i
            case JumpIf(cmp, label):
                   return i
            case _:
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
     
    def live_arg(self, a: arg) -> arg:
         match a:
            case Immediate(value):
                return None
            case Variable(id):
                return Variable(id)
            case Reg(id):
                return Reg(id)
            case Global(name):
                return a
            case Deref(reg, off):
                return a
            case _:
                raise Exception('error in assign_homes_arg, unexpected ' + repr(a))       
         

    def W_function(self, i: instr) -> set:
         res = set()
         match(i):
            case Instr('movq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('addq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('andq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('sarq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('subq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('negq', [arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Instr('xorq', [arg1, arg2]):
                   w_var = self.live_arg(arg2)
                   if w_var != None:
                        res.add(w_var)
            case Callq("read_int",0):
                   w_var = self.live_arg(Reg("rax"))
                   if w_var != None:
                        res.add(w_var)
            case Callq("print_int", 0):
                   return None
            case Callq("collect",0):
                   pass
            case IndirectCallq(func, arg_count):
                   pass
            case TailJump(func, arg_count):
                   pass
            case Callq(func, airty):
                   pass
            case Instr('cmpq', [arg1, arg2]):
                   pass
            case Instr('sete',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Instr('setne',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)  
            case Instr('setle',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var) 
            case Instr('setl',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var) 
            case Instr('setge',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var) 
            case Instr('setg',[arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var) 
            case Instr('movzbq', [arg1, arg2]):
                   w_var = self.live_arg(arg2)
                   if w_var != None:
                        res.add(w_var) 
            case Instr('leaq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Jump(label):
                   pass
            case JumpIf(cmp, label):
                   pass
            case _:
                raise Exception('error in W_function, unexpected ' + repr(i))
         return res

    def R_function(self, i: instr) -> set:
         res= set()
         match(i):
            case Instr('movq', [arg1, arg2]):
                    w_var = self.live_arg(arg1)
                    if w_var != None:
                        res.add(w_var)
            case Instr('addq', [arg1, arg2]):
                    w_var1 = self.live_arg(arg1)
                    w_var2 = self.live_arg(arg2)
                    if w_var1 != None:
                        res.add(w_var1)
                    if w_var2 != None:
                        res.add(w_var2)
            case Instr('subq', [arg1, arg2]):
                    w_var1 = self.live_arg(arg1)
                    w_var2 = self.live_arg(arg2)
                    if w_var1 != None:
                        res.add(w_var1)
                    if w_var2 != None:
                        res.add(w_var2)
            case Instr('negq', [arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Instr('xorq', [arg1, arg2]):
                   w_var = self.live_arg(arg2)
                   if w_var != None:
                        res.add(w_var)
            case Callq("read_int",0):
                   return None
            case Callq("collect",0):
                   pass
            case Callq("print_int", 0):
                   w_var = self.live_arg(Reg("rdi"))
                   if w_var != None:
                        res.add(w_var)
            case Callq(func, airty):
                   for i in range(airty):
                        res.add(self.arg_regs[i])
                   if type(func) == Variable:
                        w_var = self.live_arg(func)
                        if w_var != None:
                              res.add(w_var)
            case IndirectCallq(func, arg_count):
                   for i in range(arg_count):
                        res.add(self.arg_regs[i])
                   if type(func) == Variable:
                        w_var = self.live_arg(func)
                        if w_var != None:
                              res.add(w_var)
            case TailJump(func, arg_count):
                   if type(func) == Variable:
                        w_var = self.live_arg(func)
                        if w_var != None:
                              res.add(w_var)
                   for i in range(arg_count):
                        res.add(self.arg_regs[i])
            case Instr('cmpq', [arg1, arg2]):
                   w_var1 = self.live_arg(arg1)
                   w_var2 = self.live_arg(arg2)
                   if w_var1 != None:
                        res.add(w_var1)
                   if w_var2 != None:
                        res.add(w_var2)
            case Instr('andq', [arg1, arg2]):
                    w_var1 = self.live_arg(arg1)
                    w_var2 = self.live_arg(arg2)
                    if w_var1 != None:
                        res.add(w_var1)
                    if w_var2 != None:
                        res.add(w_var2)
            case Instr('sarq', [arg1, arg2]):
                    w_var1 = self.live_arg(arg1)
                    w_var2 = self.live_arg(arg2)
                    if w_var1 != None:
                        res.add(w_var1)
                    if w_var2 != None:
                        res.add(w_var2)
            case Instr('leaq', [arg1, arg2]):
                   pass
            case Instr('sete',[arg1]):
                   pass
            case Instr('setne',[arg1]):
                   pass 
            case Instr('setle',[arg1]):
                   pass
            case Instr('setl',[arg1]):
                   pass
            case Instr('setge',[arg1]):
                   pass
            case Instr('setg',[arg1]):
                   pass
            case Instr('movzbq', [arg1, arg2]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var) 
            case Jump(label):
                   pass
            case JumpIf(cmp, label):
                   pass
            case _:
                raise Exception('error in R_function, unexpected ' + repr(i))
         return res


    def generate_CFG(self, blocks) -> DirectedAdjList:
         cfg = DirectedAdjList()
         for x in blocks.keys():
              cfg.add_vertex(x)
         for x in blocks.keys():
              for y in blocks[x]:
                   match(y):
                        case Jump(label):
                             cfg.add_edge(x, label)
                        case JumpIf(cmp, label):
                             cfg.add_edge(x, label)
     #     print(cfg.show())
         return cfg

    def transfer(self, node, input, blocks):
     #     print("blocks-", blocks)
         ss = blocks[node]
     #     print("node-", node, "len of inst-", len(ss))
         live_var = set()
         live_dict = {}
         for x in input:
              live_var.add(x)
         if len(ss) > 0:
               live_dict[ss[len(ss)-1]] = live_var.copy()   #out-of-range exceptions ???? 
               for x in range(len(ss)-1,-1,-1):
                    i = ss[x]
                    r_vars = self.R_function(i)
                    w_vars = self.W_function(i)
                    if w_vars != None:
                         for d in w_vars:
                              live_var.discard(d)
                    if r_vars != None:
                         live_var.update(r_vars)   
                    if x != 0:
                         live_dict[ss[x-1]] = live_var.copy()
         return list(live_var), live_dict
    
    def compare_lists(self,a,b):
         if len(a) != len(b):
              return False
         for b1 in b:
              if b1 not in a:
                   return False
         for a1 in a:
              if a1 not in b:
                   return False
         return True


    def analyze_dataflow(self, bottom, blocks, cgf: DirectedAdjList, name:str):
         cgf_transpose = transpose(cgf)
         mapping = dict((v, ([], {})) for v in cgf.vertices())
         worklist = deque()
         for x in cgf.vertices():
              worklist.append(x)
         while len(worklist) > 0:
          #     print("current worklist before pop-", worklist)
              node = worklist.pop()
              if node == name+'_conclusion':
                   continue
              inputs= []
              for v in cgf_transpose.adjacent(node):
               #     print("Adjacent Blocks of ",node," is-", v, " appending bottom to extend-", mapping[v][0])
                   for x in mapping[v][0]:
                        if x not in inputs:
                              inputs.append(x)
              output, inst = self.transfer(node, inputs, blocks)
          #     print("\n current mapping of nore-",node," is -", mapping[node][0], " received mapping-", output)
              mapping[node] = (mapping[node][0], inst)
              if not self.compare_lists(output, mapping[node][0]):
                   mapping[node] = (output, inst)
               #     print("Updated Mappings-", mapping)
                   for x in cgf.adjacent(node):
                         worklist.append(x)
         return mapping

                           

    def uncover_live(self, ss: List[instr], block, live_before, live_dict, live_block, cgf: DirectedAdjList) -> dict:
         live_var = set()
         for e in cgf.out[block]:
              if e in live_before.keys():
                for e1 in live_before[e] :
                    live_var.add(e1)
         live_dict[ss[len(ss)-1]] = live_var.copy()
         for x in range(len(ss)-1,-1,-1):
            i = ss[x]
            r_vars = self.R_function(i)
            w_vars = self.W_function(i)
            print("for instr-", i, " read are-", r_vars, " | write are- ",w_vars)
            print("live variables before - ", live_var)
            if w_vars != None:
                for d in w_vars:
                    live_var.discard(d)
            if r_vars != None:
                live_var.update(r_vars)
            print("live variables after - ", live_var)
            if x != 0:
                live_dict[ss[x-1]] = live_var.copy()
            live_before[block] = live_var
            live_block[block] = live_dict
    
    def isMovqInstr(self, i: instr) -> bool:
         match(i):
              case Instr('movq', [arg1, arg2]):
                   return True
              case _:
                   return False
              
    def isCallqInstr(self, i:instr) -> bool:
          match(i):
            case Callq(str, args):
                    return True
            case IndirectCallq(func, args):
                    return True
            case TailJump(func, arg_count):
                    return True
            case _:
                    return False
    
    def isCall(self, i: instr) -> bool:
         match(i):
              case Callq("collect", 0):
                  return True
              case Callq("read_int",0):
                   return False
              case Callq("print_int", 0):
                   return False
              case Callq(func, airty):
                   return True  # call to user-defined function 
              case IndirectCallq(func, args):
                    return True # call to user-defined function
              case TailJump(func, arg_count):
                    return True # call to user-defined function
              case _:
                  return False
               
    def AddEdgesToRegisters(self, vars: set, graph: UndirectedAdjList, name: str) -> UndirectedAdjList:
         regs = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]
         for x in vars:
              for r in regs:
                   if x != Reg(r) and type(x) != Global:
                    graph.add_edge(x, Reg(r))
                   else:
                        if x in self.unused_callee[name]:
                             self.unused_callee[name].remove(x)
         return graph
    
    def AddEdgesToCalleeRegisters(self, vars: Variable, graph: UndirectedAdjList) -> UndirectedAdjList:
         print("Adding edges to callee registers for tuple-", vars)
         for r in self.callee_save:
               graph.add_edge(vars, r)
         return graph
    
    def build_move_biase(self, graph, ss: List[instr]) -> UndirectedAdjList:
         for s in ss:
            match(s):
                case Instr('movq', [arg1, arg2]):
                        if type(arg1) != Immediate and type(arg2) != Immediate:
                            graph.add_edge(arg1, arg2)
                case Instr('movzbq', [arg1, arg2]):
                        if type(arg1) != Immediate and type(arg2) != Immediate:
                             if arg1 == Reg('al') and arg2 != Reg('rax'):
                                  graph.add_edge(Reg('rax'), arg2)
                case _:
                    continue
         return graph      
                
    
    def build_interference(self, block_inst, name) -> UndirectedAdjList:
         graph = UndirectedAdjList()
     #     print("BUILD INTERFERENCE -------------------------------------\n")
         for b in block_inst.keys():
            mapping = block_inst[b][1] # due to result from liveness analysis
            for x in mapping.keys():
                match(x):
                        case Instr(str, [arg1, arg2]):
                                if type(arg2) != Immediate and type(arg2) != Global:
                                    graph.add_vertex(arg2) #create a vertex for all W(k) to be coloured
                        case Instr('negq', [arg1]):
                                if type(arg1) != Immediate and type(arg1) != Global:
                                    graph.add_vertex(arg1)
                        case Instr('xorq', [arg1, arg2]):
                                if type(arg1) != Immediate and type(arg1) != Global:
                                    graph.add_vertex(arg2)
                        
                if self.isCallqInstr(x) and self.isCall(x):
                         # print("callq inst-", [x])
                         # print("Callq inst with live variables- ", mapping[x])
                         for y in mapping[x]:
                              # print("live vars on collect-", [y])   #all the call-live variables should have edge to callee-save and caller-save registers
                              if type(y) == Variable and type(self.varTypes[name][y.id]) == TupleType:
                                   graph = self.AddEdgesToCalleeRegisters(y, graph)
                                   graph = self.AddEdgesToRegisters(set([y]), graph, name)
                              else:
                                   graph = self.AddEdgesToRegisters(set([y]), graph, name)
                elif self.isCallqInstr(x):
                    #  print("callq inst-", [x])
                     graph = self.AddEdgesToRegisters(mapping[x], graph, name)
                else: 
                        for y in mapping[x]:
                            match(x):
                                case Instr('movq', [arg1, arg2]):
                                    if type(y) != Global and y!= arg1 and y!=arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                            graph.add_edge(y, arg2)
                                case Instr('leaq', [arg1, arg2]):
                                    if type(y) != Global and y!=arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                            graph.add_edge(y, arg2)
                                case Instr('addq', [arg1, arg2]):
                                    if type(y) != Global and y != arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                        graph.add_edge(y, arg2)
                                case Instr('subq', [arg1, arg2]):
                                    if type(y) != Global and y != arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                        graph.add_edge(y, arg2)
                                case Instr('negq', [arg1]):
                                    if type(y) != Global and y != arg1 and type(arg1) != Immediate and type(arg1) != Global:
                                            graph.add_edge(y, arg1)
                                case Instr('xorq', [arg1, arg2]):
                                    if type(y) != Global and y != arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                            graph.add_edge(y, arg2)
                                case Instr('cmpq', [arg1, arg2]):
                                    if type(y) != Global and y!= arg1 and type(arg1) != Immediate and type(arg1) != Global:
                                            graph.add_edge(y, arg1)
                                    if type(y) != Global and y!=arg2 and type(arg2) != Immediate and type(arg2) != Global:
                                            graph.add_edge(y, arg2)
                                           
     #     print("-------------END INTERFERENCE--------------------------------------------")
         return graph
    
    def precolour_registers(self, graph:UndirectedAdjList, sat: dict, pq: PriorityQueue, name:str) -> dict:
         vert = graph.vertices()
         reg = {}
         registers = {Reg("rax"): -1, Reg("rsp"): -2, Reg("rbp"): -3, Reg("r11"): -4, Reg("r15"): -5, Reg("rcx"): 0, Reg("rdx"): 1, Reg("rsi"): 2, Reg("rdi"): 3, Reg("r8"): 4, Reg("r9"): 5,
                      Reg("r10"): 6, Reg("rbx"): 7, Reg("r12"): 8, Reg("r13"): 9, Reg("r14"): 10 }
         for v in vert:
              if type(v) == Reg and v in registers.keys():
                    reg[v] = registers[v]
                    for adj in graph.adjacent(v):
                        if type(adj) == Reg:
                                continue
                        if registers[v] not in sat[adj]:
                              sat[adj].append(registers[v])
                              pq.increase_key(adj)
                    if registers[v] in self.callee_save and registers[v] not in self.used_callee[name] and registers[v] not in self.unused_callee:
                         self.used_callee[name].append(registers[v])  #increment the count of used callee save registers 
     #     print("Colouring Registers - ", reg, " and the sat list for vertices - ", sat)      
         return reg, sat
    

    def checkColour(self, v, color, name):
         if type(v) == Variable and v.id in self.varTypes[name]:
               return (( type(self.varTypes[name][v.id]) != TupleType and color not in self.tupleColors) or ( type(self.varTypes[name][v.id]) == TupleType and color not in self.varColors ))
         if type(v) == Deref:
              return (color not in self.tupleColors)
         return False
              

    def color_graph(self, graph:UndirectedAdjList, move_graph:UndirectedAdjList, name:str ) -> dict:
         vert = graph.vertices()
     #     print(graph.show())
     #     print("Graph Vertices:", vert)
         sat = {}
         color_v = {}
         precoloured_registers = {Reg("rax"): -1, Reg("rsp"): -2, Reg("rbp"): -3, Reg("r11"): -4, Reg("r15"): -5, Reg("al"): -1, Reg("ah"): -1}
         callee_registers = { 7: Reg("rbx"), 8:Reg("r12"), 9:Reg("r13"), 10:Reg("r14"), -3: Reg("rbp"), -5:Reg("r15") }
         registers_list = ["rsp", "rbp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "al", "ah"]
         def compare(u,v):
            u = u.__repr__().split("@")[0]
            if 'free_ptr' in u:
                 u = self.getGlobal("free_ptr")
            elif 'fromspace_end' in u:
                 u = self.getGlobal("fromspace_end")
            elif 'rip' in u:
                 u = self.getGlobal(u)
            elif u[0].isdigit():
                 ind = u.index("("); off = u[:ind]; reg= u[ind+2:len(u)-1]
                 u = Deref(reg, int(off))
            elif u[1:] in registers_list:
                 u = Reg(u[1:])
            else:
                 u = Variable(u)
            v = v.__repr__().split("@")[0]
            if 'free_ptr' in v:
                 v = self.getGlobal("free_ptr")
            elif 'fromspace_end' in v:
                 v = self.getGlobal("fromspace_end")
            elif 'rip' in v:
                 v = self.getGlobal(v)
            elif v[0].isdigit():
                 ind = v.index("("); off = v[:ind]; reg= v[ind+2:len(v)-1]
                 v = Deref(reg, int(off))
            elif v[1:] in registers_list:
                 v = Reg(v[1:])
            else:
                 v = Variable(v)
          #   print("comparing the lengths of sat of u-",[u]," and v-",[v])
            if  len(sat[u]) == len(sat[v]):
                 u_colours = []
                 v_colours = []
                 for x in move_graph.adjacent(u):
                      if x in color_v.keys() and color_v[x] not in sat[u] and color_v[x] >= 0:
                           u_colours.append(color_v[x])
                 for x in move_graph.adjacent(v):
                      if x in color_v.keys() and color_v[x] not in sat[v] and color_v[x] >= 0:
                           v_colours.append(color_v[x])
                 return len(u_colours) < len(v_colours)
                           
            else:
                 return  len(sat[u]) < len(sat[v])
         pq = PriorityQueue(compare)
         for v in vert:
              if v not in sat.keys():
                   sat[v] = []
         for v in vert:
            pq.push(v)
         
         color_v, sat = self.precolour_registers(graph, sat, pq, name)
         while not pq.empty():
              v = pq.pop()
              if type(v) == Reg:
                   continue
              if type(v) == Global:
                   continue
              min_val = float("inf")
              for x in move_graph.adjacent(v):
                   if x in color_v.keys() and color_v[x] not in sat[v] and color_v[x] >= 0:
                    #     print(type(v), " is the type of cur_var ")
                        if self.checkColour(v, color_v[x], name) and color_v[x] < min_val: # avoid assigning Tuple colours to other Variables
                              min_val = color_v[x] #assign a minimum color that is available from the move instructions 
              print("Assigned min-val:", min_val," to arg:", v," from the move graph with sat matrix-", sat[v])
              if min_val == float("inf"):
                for x in range(0,MAX_REG):
                    if x not in sat[v] and self.checkColour(v, x, name):
                            min_val = x
                            break
              print("Assigned min-val:", min_val," to arg:", v," from the min range with sat mat-",sat[v])
              if min_val in callee_registers.keys():
                   if callee_registers[min_val] not in self.used_callee[name]:
                    self.used_callee[name].append(callee_registers[min_val])
                   if callee_registers[min_val] in self.unused_callee:
                    self.unused_callee[name].remove(callee_registers[min_val])
              color_v[v] = min_val
              if type(v) == Variable and v.id in self.varTypes[name] and type(self.varTypes[name][v.id]) == TupleType:
                   self.tupleColors.append(min_val)
              else:
                   self.varColors.append(min_val)
          #     print("Tuple colours-", self.tupleColors, "Variable COlors-", self.varColors,"\n")
              for adj in graph.adjacent(v):
                   if adj in precoloured_registers.keys():
                        continue
                   if min_val not in sat[adj]:
                         sat[adj].append(min_val)
                         pq.increase_key(adj)
         print("\n Assigned colour vals-", color_v, " and the updated sat list-", sat,"\n")
         return color_v
    
    def assign_registers(self, color_v:dict, name: str) -> dict:
         registers = {0:Reg("rcx"), 1:Reg("rdx"), 2:Reg("rsi"), 3:Reg("rdi"), 4:Reg("r8"), 5:Reg("r9"),
                      6: Reg("r10"), 7: Reg("rbx"), 8:Reg("r12"), 9:Reg("r13"), 10:Reg("r14"), -1:Reg("rax"), -2:Reg("rsp"), -3: Reg("rbp"), -4: Reg("r11"), -5:Reg("r15")} # removed -4: Reg("r11"), -5:Reg("r15") {TUPLES}
         colors_mem = {}
         reg_var = {}
         dref_counter = -8 * len(self.used_callee[name]) # should be placed below the callee saved registers. 
         root_counter = 0
         for var in color_v.keys():
              if color_v[var] in registers.keys():
                reg_var[var] = registers[color_v[var]]
                if registers[color_v[var]] in self.callee_save and registers[color_v[var]] not in self.used_callee[name] and registers[color_v[var]] not in self.unused_callee[name]:
                     self.used_callee[name].append(registers[color_v[var]])
              elif color_v[var] in colors_mem.keys():
                     reg_var[var] = colors_mem[color_v[var]]
              else:
                     if type(var) == Reg or type(var) == Global:
                          continue
                     print("master list-", self.varTypes)
                     print("cur_fun-", self.varTypes[name])
                     print("Accessing variabels from fun-", name, " and accessing var - ", var)
                     if type(var) == Variable and type(self.varTypes[name][var.id]) == TupleType:
                         #  print("Adding to root space-", var)
                          root_counter = root_counter - 8
                          reg_var[var] = Deref("r15", root_counter)
                          colors_mem[color_v[var]] = Deref("r15", root_counter)
                          self.root_stack[name] = self.root_stack[name] + 1 # count of spilled tuples
                     else:
                         #  print("Adding to stack space-", var)
                          dref_counter = dref_counter - 8
                          reg_var[var] = Deref("rbp", dref_counter)
                          colors_mem[color_v[var]] = Deref("rbp", dref_counter)
                          self.stack_space[name] = self.stack_space[name] + 1 #count of stack variables
     #     print("Used callee-save - ", self.used_callee)     
         return reg_var
                       

    def assign_homes_instrs(self, blocks, cfg: DirectedAdjList, fun_name: str,
                            home: Dict[Variable, arg]) -> List[instr]:
        live_before = {}
        move_grph_blocks = {}
        live_block = {}
        move_graph = UndirectedAdjList()
        liveness_analyze = self.analyze_dataflow([], blocks, transpose(cfg), fun_name)
        for x in blocks:
            if x == fun_name+"_conclusion":
                 continue
            ss = blocks[x]
            move_graph = self.build_move_biase(move_graph, ss)
            move_grph_blocks[x] = move_graph
        print("Liveneess Alaysis- ")
     #    for x in liveness_analyze:
     #         print("\n")
     #         print(x," : ", liveness_analyze[x][0])
     #         inst = liveness_analyze[x]
     #         for y in inst[1:]:
     #              for z in y.keys():
     #                print(z," : ", y[z])
        print("-----------------------------------------------------------")
        graph = self.build_interference(liveness_analyze, name=fun_name)
     #    print(graph.show())
        color = self.color_graph(graph, move_graph, name=fun_name)
        registers = self.assign_registers(color_v=color, name=fun_name)
        block_result = {}
        for x in blocks:
             if x == fun_name+"_conclusion":
                  continue
             res = []
             ss = blocks[x]
             for s in ss:
                temp = self.assign_homes_instr(s, registers)
                res.append(temp)
             block_result[x] = res
        return block_result
    

    def assign_homes(self, p: X86ProgramDefs) -> X86ProgramDefs:
        match p:
            case X86ProgramDefs(body):
                functions = []
                for x in body:
                     match x:
                          case FunctionDef(name, [], blocks, None, returns, None):
                               cfg = self.generate_CFG(blocks)
                               self.stack_space[name] = 0; self.root_stack[name] = 0; self.used_callee[name] = []; self.unused_callee[name] = [Reg("rsp"), Reg("rbp"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"), Reg("r15")] # initialise
                               res = self.assign_homes_instrs(blocks, cfg, name, {})
                               functions.append(FunctionDef(name, [], res, None, returns, None))
                          case _:
                               raise Exception('error in assign_homes, unexpected program defs' + repr(p))
                return X86ProgramDefs(functions)
            case _:
                raise Exception('error in assign_homes, unexpected ' + repr(p))  
              

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        res = []
        match(i):
            case Instr('movq', [arg1, arg2]):
                    if arg1 == arg2:
                         return res #Ignore this instruction
                    if type(arg1) == Deref and type(arg2) == Deref:
                         arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                         arg2_stmt = Instr('movq', [Reg("rax"), arg2]) 
                         res.append(arg1_stmt)
                         res.append(arg2_stmt)
                    elif (type(arg1) == Deref and type(arg2) == Immediate) or (type(arg2) == Deref and type(arg1) == Immediate):
                         if type(arg2) == Immediate and int(arg2.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg2, Reg("rax")])
                              arg2_stmt = Instr('movq', [Reg("rax"), arg1])
                              res.append(arg1_stmt)
                              res.append(arg2_stmt)  
                         elif type(arg1) == Immediate and int(arg1.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                              arg2_stmt = Instr('movq', [Reg("rax"), arg2])  
                              res.append(arg1_stmt)
                              res.append(arg2_stmt)  
                         else:
                              res.append(i)
                    else:
                         res.append(i)                      
            case Instr('addq', [arg1, arg2]):
                    if type(arg1) == Deref and type(arg2) == Deref:
                         arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                         arg2_stmt = Instr('addq', [Reg("rax"), arg2])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt)
                    elif (type(arg1) == Deref and type(arg2) == Immediate) or (type(arg2) == Deref and type(arg1) == Immediate):
                         if type(arg2) == Immediate and int(arg2.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg2, Reg("rax")])
                              arg2_stmt = Instr('addq', [Reg("rax"), arg1])
                              res.append(arg1_stmt)
                              res.append(arg2_stmt)  
                         elif type(arg1) == Immediate and int(arg1.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                              arg2_stmt = Instr('addq', [Reg("rax"), arg2])  
                              res.append(arg1_stmt)
                              res.append(arg2_stmt) 
                         else:
                              res.append(i)
                    else:
                         res.append(i)     
            case Instr('subq', [arg1, arg2]):
                    if type(arg1) == Deref and type(arg2) == Deref:
                         arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                         arg2_stmt = Instr('subq', [Reg("rax"), arg2])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt) 
                    elif (type(arg1) == Deref and type(arg2) == Immediate) or (type(arg2) == Deref and type(arg1) == Immediate):
                         if type(arg2) == Immediate and int(arg2.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg2, Reg("rax")])
                              arg2_stmt = Instr('subq', [Reg("rax"), arg1])
                              res.append(arg1_stmt)
                              res.append(arg2_stmt)  
                         elif type(arg1) == Immediate and int(arg1.__str__().removeprefix("$")) > pow(2,16):
                              arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                              arg2_stmt = Instr('subq', [Reg("rax"), arg2])
                              res.append(arg1_stmt)
                              res.append(arg2_stmt) 
                         else:
                              res.append(i)
                    else:
                         res.append(i) 
            case Instr('movzbq', [arg1, arg2]):
                    registers = [Reg("rax"), Reg("rsp"), Reg("rbp"), Reg("r11"), Reg("r15"), Reg("rcx"), Reg("rdx"), Reg("rsi"), Reg("rdi"), Reg("r8"), Reg("r9"),
                      Reg("r10"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14") ]
                    boolRegisters = [Reg('al'), Reg('ah'), Reg('bl'), Reg('bh'), Reg('cl'), Reg('ch'), Reg('dl'), Reg('dh')]
                    byteRegister = {Reg('al'): Reg('rax'), Reg('ah'): Reg('rax'), Reg('bl'): Reg('rbx'), Reg('bh'): Reg('rbx'), Reg('cl'): Reg('rcx'), Reg('ch'): Reg('rcx'), Reg('dl'): Reg('rdx'), Reg('dh'): Reg('rdx')}
                    if arg2 in boolRegisters:
                            res = []
                            res.append(i)
                            res.append(Instr('movzbq', [arg1, byteRegister[arg2]]))
                    elif type(arg2) == Deref and arg1 in boolRegisters:
                            res = []
                            res.append(Instr('movzbq', [arg1, byteRegister[arg1]]))
                            res.append(Instr('movq', [byteRegister[arg1], arg2]))
                    else:
                         res.append(i)
            case Instr('cmpq', [arg1, arg2]):
                  if type(arg1) == Deref and type(arg2) == Deref:
                         arg1_stmt = Instr('movq', [arg2, Reg("rax")])
                         arg2_stmt = Instr('cmpq', [arg1, Reg("rax")])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt) 
                  elif type(arg1) == Immediate and type(arg2) == Immediate:
                         arg1_stmt = Instr('movq', [arg2, Reg("rax")])
                         arg2_stmt = Instr('cmpq', [arg1, Reg("rax")])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt)  
                  else:
                       res.append(i) 
            case Instr('leaq', [arg1, arg2]): 
                  if type(arg2) != Reg:
                         arg1_stmt = Instr('movq', [arg2, Reg("rax")]) #can we hard-code this way ? 
                         arg2_stmt = Instr('leaq', [arg1, Reg("rax")])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt)
                  else:
                       res.append(i)
            case TailJump(func, arg_count):
                  if func != Reg("rax"):
                       arg1_stmt = Instr('movq', [func, Reg("rax")])
                       arg2_stmt = TailJump(Reg("rax"), arg_count)
                       res.append(arg1_stmt)
                       res.append(arg2_stmt)
                  else:
                       res.append(TailJump(func, arg_count))
            case _:
                  res.append(i)   
        return res    

    def patch_instrs(self, blocks, name: str) -> List[instr]:
        block_result = {}
        for x in blocks.keys():
            if x == name+'_conclusion':
                 continue
          #   print("Accessing patch for block:", x)
            res = []
            ss = blocks[x]
            for s in ss:
                temp = self.patch_instr(s)
                for t in temp:
                    res.append(t)
            block_result[x] = res
          #   print("================== END BLOCK=====================")
        return block_result        

    def patch_instructions(self, p: X86ProgramDefs) -> X86ProgramDefs:
       match p:
            case X86ProgramDefs(body):
                functions = []
                for x in body:
                     match x:
                          case FunctionDef(name, [], blocks, None, returns, None):
                              res = self.patch_instrs(blocks, name)
                              functions.append(FunctionDef(name, [], res, None, returns, None))
                          case _:
                               raise Exception('error in patch_instructions, unexpected fun refs' + repr(p))
                return X86ProgramDefs(functions)
            case _:
                raise Exception('error in patch_instructions, unexpected ' + repr(p))        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def addressTailJmps(self, blocks, cur_block, name, final_count):
         ins = blocks[cur_block]
     #     print("finding TailJmp in block-", cur_block)
         res = []
         for i in ins:
          #     print("encountering inst-", [i])
              match i:
                   case TailJump(func, arg_count):
                        conclude_inst = self.generateConclusion(True, name, final_count)
                        for x in conclude_inst:
                             res.append(x)
                   case _:
                        res.append(i)
     #     print("----------------------END block -------------------------")
         return res
    
    def generateConclusion(self, isTailJump, name, final_count):
          conlude_inst = []
          conlude_inst.append(Instr("subq", [Immediate(8*self.root_stack[name]), Reg("r15")]))
          conlude_inst.append(Instr("addq", [Immediate(final_count), Reg("rsp")]))
          for x in self.used_callee[name]:
               if x == Reg('rbp') or x == Reg('rsp'):
                    continue
               conlude_inst.append(Instr('popq', [x])) # pop the callee save registers from memory
          conlude_inst.append(Instr('popq', [Reg("rbp")]))
          if isTailJump:
               conlude_inst.append(IndirectJump(Reg("rax"))) # if the function ends with a Tail Jump
          else:
               conlude_inst.append(Instr('retq', []))
          return conlude_inst
    
    
    def prelude_and_conclusion(self, p: X86ProgramDefs) -> X86Program:
          match p:
            case X86ProgramDefs(body):
                finalBlocks = {}
                for x in body:
                     match x:
                          case FunctionDef(name, [], blocks, None, returns, None):
                                print("Used Calle Count:", self.used_callee[name], " Stack Space:", self.stack_space[name])
                                align_count = 8 * len(self.used_callee[name]) + 8 * self.stack_space[name]
                                align_count = align(align_count,16)
                                final_count = align_count - (8 * len(self.used_callee[name]))
                                res = {}
                                # --------- PRELUDE
                                main_inst = []
                                main_inst.append(Instr('pushq', [Reg("rbp")]))
                                main_inst.append(Instr("movq",[Reg("rsp"),Reg("rbp")]))
                                for x in self.used_callee[name]:
                                     if x == Reg('rbp') or x == Reg('rsp'):
                                          continue
                                     main_inst.append(Instr('pushq', [x])) # push the callee save registers to stacks, pushq inst will automatically adjust to stack memory
                                main_inst.append(Instr("subq", [Immediate(final_count), Reg("rsp")]))
                                if name == "main":
                                   main_inst.append(Instr("movq", [Immediate(65536), Reg("rdi")]))
                                   main_inst.append(Instr("movq", [Immediate(16), Reg("rsi")])) #its marked 65536 in textbook ? 
                                   main_inst.append(Callq('initialize',0))
                                   main_inst.append(Instr("movq", [Global("rootstack_begin"), Reg("r15")]))
                                main_inst.append(Instr("movq", [Immediate(0), Deref('r15',0)]))
                                main_inst.append(Instr("addq", [Immediate(8*self.root_stack[name]), Reg('r15')]))
                                main_inst.append(Jump(name+"_start"))
                                res[label_name(name)] = main_inst
                                # --------- PROGRAM
                                for block in blocks.keys():
                                     block_inst = self.addressTailJmps(blocks, block, name, final_count)
                                     res[block] = block_inst
                                # CONCLUDE
                                conclude_inst = self.generateConclusion(False, name, final_count)
                                res[label_name(name+'_conclusion')] = conclude_inst
                                for block in res.keys():
                                   finalBlocks[block] = res[block]
          return  X86Program(finalBlocks)
    
    ############################################################################
    # Challenge - Ex-2.7 Partial Evaluators
    ############################################################################

    def pe_neg(self, r: expr):
         match r:
              case Constant(r):
                   return Constant(neg64(r))
              case _:
                   return UnaryOp(USub(), r)
            
    def pe_add(self, r1:expr, r2:expr):
         match(r1,r2):
              case (Constant(r1), Constant(r2)):
                   return Constant(add64(r1,r2))
              case _:
                   return BinOp(r1, Add(), r2)
    
    def pe_sub(self, r1:expr, r2:expr):
         match(r1,r2):
              case (Constant(r1), Constant(r2)):
                   return Constant(sub64(r1,r2))
              case _:
                   return BinOp(r1, Sub(), r2)       

    def pe_exp(self, e: expr) -> expr:
            match e:
                case BinOp(left, Add(), right):
                   pe = self.pe_add(left,right)
                   if type(pe) == Constant:
                        return pe
                   else:
                        return e
                case BinOp(left, Sub(), right):
                   pe = self.pe_sub(left,right)
                   if type(pe) == Constant:
                        return pe
                   else:
                        return e
                case UnaryOp(USub(), v):
                     pe = self.pe_neg(v)
                     if type(pe) == Constant:
                            return pe
                     else:
                            return e
                case IfExp(test, body, orelse):
                    res = self.pe_exp(test)
                    body_exp = self.pe_exp(body)
                    or_exp = self.pe_exp(orelse)
                    return IfExp(res, body_exp, or_exp)
                case BoolOp(And(), values):
                    i=0
                    res = []
                    print("processing Bool and with values-",Expr(values))
                    left = values[0]; right = values[1]
                    l = self.pe_exp(left)
                    r = self.pe_exp(right)
                    return IfExp(l, r, Constant(False))
                case BoolOp(Or(), values):
                    i=0
                    res = []
                    print(Expr(values))
                    left = values[0]; right = values[1]
                    l = self.pe_exp(left)
                    r = self.pe_exp(right)
                    return IfExp(l, Constant(True), r)
                case UnaryOp(Not(), v):
                    val = self.pe_exp(v)
                    return (UnaryOp(Not(), val))
                case Compare(left, [cmp], [right]):
                    l = self.pe_exp(left)
                    r = self.pe_exp(right)
                    return Compare(l, [cmp], [r])
                case Constant(value):
                    return (e)
                case Call(Name('input_int'), []):
                    return (e)
                case Name(id):
                    return (e)
                case Tuple(es, Load()):
                    es_exp = []
                    for e in es:
                         es_exp.append(self.pe_exp(e))
                    return Tuple(es_exp, Load())
                case Subscript(tup, index, Load()):
                    t = self.pe_exp(tup)
                    n = self.pe_exp(index)
                    return Subscript(t, n, Load())
                case Call(Name('len'), [tup]):
                    t = self.pe_exp(tup)
                    return Call(Name('len'), [t])
                case Lambda(var, exp):
                    exp_s = self.pe_exp(exp)
                    return Lambda(var, exp_s)
                case Call(Name('arity'), [exp]):
                    t_s = self.pe_exp(exp)
                    return Call(Name('arity'), [t_s])
                case Call(func, args):
                    pe_func = self.pe_exp(func)
                    pe_args = []
                    for a in args:
                         pe_args.append(self.pe_exp(a))
                    return Call(pe_func, pe_args)
                case FunRef(id, arity):
                      return e
                case Allocate(length, typ):
                    return e
                case GlobalValue(name):
                    return e 
                case _:
                    return (e)

    def pe_stmt(self, s: stmt) -> stmt:
        match s:
            case Expr(Call(Name('print'), [arg])):
                print_stmt = Expr(Call(Name('print'), [self.pe_exp(arg)])) 
                return (print_stmt)
            case Expr(value):
                exp_stmt = self.pe_exp(value)
                return (exp_stmt)
            case Assign([Name(id)], value):
                assign_stmt = Assign([Name(id)], self.pe_exp(value))
                return (assign_stmt)
            case If(test, body, orelse):
                  body_exp = []
                  for b in body:
                    body_exp.append(self.pe_stmt(b))
                  or_exp = []
                  for o in orelse:
                    or_exp.append(self.pe_stmt(o))
                  return If(test, body_exp, or_exp)
            case While(test, body, []):
                  body_exp = []
                  for b in body:
                    body_exp.append(self.pe_stmt(b))
                  test_exp = self.pe_exp(test)
                  return While(test_exp, body_exp, [])
            case Collect(size):
                  return s
            case Assign([Subscript(tup, index, Store())], value):
                  tup_exp = self.pe_exp(tup)
                  ind_exp = self.pe_exp(index)
                  val = self.pe_exp(value)
                  return Assign([Subscript(tup_exp, ind_exp, Store())], val)
            case Return(exp):
                  pe_exp = self.pe_exp(exp)
                  return Return(pe_exp)
            case AnnAssign(var, type, exp, simple):
                    exp_s = self.pe_exp(exp)
                    return AnnAssign(var, type, exp_s, simple)
            case FunctionDef(name, params, bod, dl, returns, comment):
                  pe_params = []
                  pe_body = []
                  for s in bod:
                       pe_body.append(self.pe_stmt(s))
                  return FunctionDef(name, params, pe_body, dl, returns, comment)         
            case _:
                raise Exception('error in pe_stmt, unexpected ' + repr(s))
             
    def pe_P(self, p: Module) -> Module:
         match p:
              case Module(body):
                   new_body = [self.pe_stmt(s) for s in body]
                   return Module(new_body)
              case _:
                   raise Exception('error in  pe_P, unexpected ' + repr(p))
                   
      
    ############################################################################
    # Challenge - Ex-4.7 Move Biasing
    ############################################################################