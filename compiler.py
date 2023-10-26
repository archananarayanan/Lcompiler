import ast
from ast import *
from graph import *
from priority_queue import PriorityQueue
from utils import * 
from x86_ast import *
import os
import copy
from typing import Tuple as TupleType, List, Set, Dict


Binding = TupleType[Name, expr]
Temporaries = List[Binding]
MAX_REG = 100

class Compiler:
    
    stack_space = 0
    root_stack = 0
    used_callee = []
    callee_save = [Reg("rsp"), Reg("rbp"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"), Reg("15")]
    

    ############################################################################
    # Shrink the Lif 
    ############################################################################
    
    def shrink_exp(self, s: expr) -> expr:
          print("Received Shrink exp:", type(s))
          match s:
                case IfExp(test, body, orelse):
                    res = self.shrink_exp(test)
                    body_exp = self.shrink_exp(body)
                    or_exp = self.shrink_exp(orelse)
                    return IfExp(res, body_exp, or_exp)
                case BoolOp(And(), values):
                    i=0
                    res = []
                    print("processing Bool and with values-",Expr(values))
                    left = values[0]; right = values[1]
                    l = self.shrink_exp(left)
                    r = self.shrink_exp(right)
                    return IfExp(l, r, Constant(False))
                case BoolOp(Or(), values):
                    i=0
                    res = []
                    print(Expr(values))
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
                    print("Compare Inst:", s)
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
                    # use a list for mutability
                    print(s)
                    es_s = []
                    for e in es:
                         es_s.append(self.shrink_exp(e))
                    return Tuple(es_s, Load())
                case Subscript(tup, index, Load()):
                    print("calling shrink on args-", type(tup), type(index))
                    t_s = self.shrink_exp(tup)
                    n_s = self.shrink_exp(index)
                    return Subscript(t_s, n_s, Load())
                case Call(Name('len'), [tup]):
                    t_s = self.shrink_exp(tup)
                    return Call(Name('len'), [t_s])
                case Allocate(length, typ):
                    return s
                case GlobalValue(name):
                    return s
                case _ :
                    raise Exception('error in shrink exp, unexpected ' + repr(s)) 
               
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case If(test, body, orelse):
                print("Received IF Shrink stmt:", s)
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
            case Assign([Subscript(tup, index)], value):
                    tup_s = self.shrink_exp(tup)
                    index_s = self.shrink_exp(index)
                    val_s = self.shrink_exp(value)
                    return Assign([Subscript(tup_s, index_s)], val_s)
            case _:
                print("Received Shrink stmt:", s)
                return self.shrink_exp(s)
              
    def shrink(self, p):
            match p:
                case Module(body):
                    res = [] 
                    for x in body:
                        res.append(self.shrink_stmt(x))
                    return Module(res)
                case _ :
                    raise Exception('error in shrink main module, unexpected ' + repr(p))
                       
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
                case Tuple(es, Load()):
                    # use a list for mutability
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
                    begin_stms.append(If(Compare(BinOp(GlobalValue('free_ptr'),Add(),Constant(bytes_req)),[Lt()],[GlobalValue('fromspace_end')]), [], [Collect(bytes_req)]))
                    tuple = generate_name('alloc')
                    begin_stms.append(Assign([Name(tuple)],Allocate(Constant(t_len), e.has_type)))
                    for ind in range(len(temp_var)):
                         begin_stms.append(Assign([Subscript(Name(tuple), Constant(ind), Load())], Name(temp_var[ind])))
                    return Begin(begin_stms, Name(tuple))
                case Subscript(tup, index, Load()):
                    tup_rco = self.expose_alloc_exp(tup)
                    ind_rco = self.expose_alloc_exp(index)
                    return Subscript(tup_rco, ind_rco, Load())
                case Call(Name('len'), [tup]):
                    tup_rco = self.expose_alloc_exp(tup)
                    return Call(Name('len'), [tup_rco])
                case Allocate(length, typ):
                    len_rco = self.expose_alloc_exp(length)
                    return Allocate(len_rco, typ)
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
            case Assign([Subscript(tup, index)], value):
                  t_atm = self.expose_alloc_exp(tup)
                  i_atm = self.expose_alloc_exp(index)
                  val_atm = self.expose_alloc_exp(value)
                  res.append(Assign([Subscript(t_atm, i_atm)], val_atm))
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

    def rco_exp(self, e: expr, need_atomic: bool) -> TupleType[expr, Temporaries]:
            print("encountering expression-", e)
            match e:
                case BinOp(left, Add(), right):
                    l = self.rco_exp(left, True)
                    r = self.rco_exp(right, True)
                    if need_atomic:
                         var = generate_name("temp")
                         temp = l[1]
                         for y in r[1]:
                              temp.append(y)
                         temp.append((Name(var), BinOp(l[0] , Add(), r[0])))
                         return (Name(var), temp)
                    else:
                         return (BinOp(l[0], Add(), r[0]),[])
                case BinOp(left, Sub(), right):
                    l = self.rco_exp(left, True)
                    r = self.rco_exp(right, True)
                    if need_atomic:
                         var = generate_name("temp")
                         temp = l[1]
                         for y in r[1]:
                              temp.append(y)
                         temp.append((Name(var),BinOp(l[0] , Sub(), r[0])))
                         return (Name(var), temp)
                    else:
                         return (BinOp(l[0], Sub(), r[0]),[])
                case UnaryOp(USub(), v):
                    val = self.rco_exp(v, True)
                    if need_atomic:
                         var = generate_name("temp")
                         val[1].append((Name(var), UnaryOp(USub(), val[0])))
                         return (Name(var), val[1])
                    else:
                         return (UnaryOp(USub(), val[0]), [])
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
                    if need_atomic:
                         var = generate_name("temp")
                         if body_b == None:
                              body_b = body_exp[0]
                         if or_b == None:
                              or_b = or_exp[0]
                         temp.append((Name(var), IfExp(test_exp[0], body_b, or_b)))
                         return (Name(var), temp)
                    else:
                         return (IfExp(test_exp[0], body_exp[0], or_exp[0]), temp)
                case UnaryOp(Not(), v):
                    val = self.rco_exp(v, True)
                    return (UnaryOp(Not(), val[0]), val[1])
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
                    for x in res_rco[1]:
                         temp.append(x)
                    rco_stmts = []
                    for s in stmts:
                         stmts = self.rco_stmt(s)
                         for ss in stmts:
                              rco_stmts.append(ss)
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
                case Allocate(length, typ):
                    len_rco = self.rco_exp(length, True)
                    temp = []
                    for x in len_rco[1]:
                         temp.append(x)
                    return (Allocate(len_rco[0], typ),temp)
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
            case Assign([Subscript(tup, index)], value):
                  t_atm = self.rco_exp(tup, True)
                  for i in t_atm[1]:
                       res.append(i)
                  i_atm = self.rco_exp(index, True)
                  for i in i_atm[1]:
                       res.append(i)
                  val_atm = self.rco_exp(value, True)
                  for i in val_atm[1]:
                       res.append(i)
                  res.append(Assign([Subscript(t_atm[0], i_atm[0])], val_atm[0]))
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
              case _:
                   raise Exception('error in explicate_pre, unexpected condition- ' + repr(cnd))
              
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
              case _:
               #     print("else case for exp-", s)
                   return [s] + cont
              
    def explicate_control(self, p):
         match p:
              case Module(body):
                   new_body = [Return(Constant(0))]
                   basic_blocks = {}
                   for s in reversed(body):
                        new_body = self.explicate_stmt(s, new_body, basic_blocks)
                   basic_blocks[label_name('start')] = new_body
                   return CProgram(basic_blocks)
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
                      return Global(name)
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
                  res.append(Instr('movq', [tup, Reg('r11')]))
                  ind_loc = 8*(index+1)
                  var = Deref('r11',ind_loc)
                  return var,res
            case Call(Name('len'), [tup]):
                   res.append(Instr('movq', [Deref(tup, 1), Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [1, Reg('rax')]))
                   var = Reg('rax')
                   return var,res
            case Allocate(length, typ):
                   tag = []
                   if typ == TupleType:
                        for i in range(length):
                             tag.append('1')
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   bin_tag= bin(int(tag, 2))
                   tag = int(bin_tag << 1)
                   res.append(Instr('movq', ['free_ptr(\%rip)', Reg('r11')]))
                   res.append(Instr('addq', [8*(length+1), 'free_ptr(\%rip)']))
                   res.append(Instr('movq', [Immediate(tag), Deref(Reg('r11'), 0)]))
                   var = Reg('r11')
                   return var, res
            case _:
                var = self.select_arg(e)
         return var,res
                   

    def select_stmt(self, s: stmt) -> List[instr]:
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
                  jmp_inst = Jump('conclusion')
                  res.append(mov_inst)
                  res.append(jmp_inst)
            case Assign([Subscript(tup, index)], value):
                  res.append(Instr('movq', [tup, Reg('r11')]))
                  ind_loc = 8*(index+1)
                  res.append(Instr('movq', [value, Deref('r11',ind_loc)]))
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
                  res.append(Instr('movq', [tup, Reg('r11')]))
                  ind_loc = 8*(index+1)
                  res.append(Instr('movq', [Deref('r11',ind_loc), id]))
                  return id,res
            case Call(Name('len'), [tup]):
                   res.append(Instr('movq', [Deref(tup, 1), Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [1, Reg('rax')]))
                   res.append(Instr('movq', [Reg('rax'), id]))
                   return id,res
            case Allocate(length, typ):
                   tag = []
                   if typ == TupleType:
                        for i in range(length):
                             tag.append('1')
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   bin_tag= bin(int(tag, 2))
                   tag = int((bin_tag << 1) | 1)
                   print(" obtained Tag for inst-",s," is-",tag)
                   res.append(Instr('movq', ['free_ptr(\%rip)', Reg('r11')]))
                   res.append(Instr('addq', [8*(length+1), 'free_ptr(\%rip']))
                   res.append(Instr('movq', [Immediate(tag), Deref(Reg('r11'), 0)]))
                   res.append(Instr('movq', [Reg('r11'), id]))
                   return id, res
            case _:
                   arg = self.select_arg(s)
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
                  res.append(Instr('movq', [tup, Reg('r11')]))
                  ind_loc = 8*(index+1)
                  return res, Deref('r11',ind_loc)
            case Call(Name('len'), [tup]):
                   res.append(Instr('movq', [Deref(tup, 1), Reg('rax')])) # can we  hardcode rax ? 
                   res.append(Instr('andq', [Immediate(126), Reg('rax')]))
                   res.append(Instr('sarq', [1, Reg('rax')]))
                   return res,Reg('rax')
            case Allocate(length, typ):
                   tag = []
                   if typ == TupleType:
                        for i in range(length):
                             tag.append('1')
                   pointer_length = '{0:06b}'.format(length)
                   tag = ''.join(tag)+pointer_length
                   bin_tag= bin(int(tag, 2))
                   tag = int(bin_tag << 1)
                   res.append(Instr('movq', ['free_ptr(\%rip)', Reg('r11')]))
                   res.append(Instr('addq', [8*(length+1), 'free_ptr(\%rip)']))
                   res.append(Instr('movq', [Immediate(tag), Deref(Reg('r11'), 0)]))
                   return res, Reg('r11')
            case _:
                return res,self.select_arg(s) 
            
         return res
       

    def select_interp_stmt(self, s, cont, stmts: List[stmt]) -> List[instr]:
        res = self.select_stmt(s)
        for x in res:
            stmts.append(x)
        return self.select_interp_stmts(cont, stmts)
    
    def select_interp_stmts(self, ss, stmts: List[stmt]) -> List[instr]:
        match ss:
            case []:
                return stmts
            case [s, *ss]:
                return self.select_interp_stmt(s, ss, stmts)    

    def select_instructions(self, p: Module) -> X86Program:
         match p:
            case CProgram(body):
                blocks = {}
                for (l, ss) in body.items():
                    l_stmt = []
                    l_stmt = self.select_interp_stmts(ss, l_stmt)
                    blocks[l] = l_stmt
                return X86Program(blocks)
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
            case Instr('negq', [arg1]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    inst_stmt = Instr('negq', [arg1_stmt])
                    return inst_stmt
            case Instr('xorq', [arg1]):
                    arg1_stmt = self.assign_homes_arg(arg1, reg_var)
                    inst_stmt = Instr('xorq', [arg1_stmt])
                    return inst_stmt
            case Callq("read_int",0):
                    return i
            case Callq("print_int", 0):
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
            case Instr('subq', [arg1, arg2]):
                    w_var = self.live_arg(arg2)
                    if w_var != None:
                        res.add(w_var)
            case Instr('negq', [arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Instr('xorq', [arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Callq("read_int",0):
                   w_var = self.live_arg(Reg("rax"))
                   if w_var != None:
                        res.add(w_var)
            case Callq("print_int", 0):
                   return None
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
            case Instr('xorq', [arg1]):
                   w_var = self.live_arg(arg1)
                   if w_var != None:
                        res.add(w_var)
            case Callq("read_int",0):
                   return None
            case Callq("print_int", 0):
                   w_var = self.live_arg(Reg("rdi"))
                   if w_var != None:
                        res.add(w_var)
            case Instr('cmpq', [arg1, arg2]):
                   w_var1 = self.live_arg(arg1)
                   w_var2 = self.live_arg(arg2)
                   if w_var1 != None:
                        res.add(w_var1)
                   if w_var2 != None:
                        res.add(w_var2)
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
         ss = blocks[node]
         live_var = set()
         live_dict = {}
         for x in input:
              live_var.add(x)
         live_dict[ss[len(ss)-1]] = live_var.copy()
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


    def analyze_dataflow(self, bottom, blocks, cgf: DirectedAdjList):
         cgf_transpose = transpose(cgf)
         mapping = dict((v, (bottom, {})) for v in cgf.vertices())
         worklist = deque(cgf.vertices())
         while len(worklist) > 0:
              node = worklist.pop()
              if node == 'conclusion':
                   continue
              inputs= bottom
              for v in cgf_transpose.adjacent(node):
                   for x in mapping[v][0]:
                        if x not in inputs:
                              inputs.append(x)
              output, inst = self.transfer(node, inputs, blocks)
              mapping[node] = (mapping[node][0], inst)
              if not self.compare_lists(output, mapping[node][0]):
                   mapping[node] = (output, inst)
                   worklist.extend(cgf.adjacent(node))
         return mapping

                           

    def uncover_live(self, ss: List[instr], block, live_before, live_dict, live_block, cgf: DirectedAdjList) -> dict:
         live_var = set()
         print(cgf.out[block])
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
            case Callq(str, 0):
                    return True
            case _:
                    return False
               
    def AddEdgesToRegisters(self, vars: set, graph: UndirectedAdjList) -> UndirectedAdjList:
         regs = ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]
        #  print("Adding set-",vars, " to caller registers")
         for x in vars:
              for r in regs:
                   if x != Reg(r):
                    graph.add_edge(x, Reg(r))
         return graph
    
    def AddEdgesToCalleeRegisters(self, vars: Variable, graph: UndirectedAdjList) -> UndirectedAdjList:
         for x in vars:
              for r in self.callee_save:
                    graph.add_edge(x, Reg(r))
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
                
    
    def build_interference(self, block_inst) -> UndirectedAdjList:
         graph = UndirectedAdjList()
     #     print("BUILD INTERFERENCE -------------------------------------\n")
        #  print("Block_inst keys:", block_inst.keys())
         for b in block_inst.keys():
          #   print("Block insts for block-",b," are-", block_inst[b],"\n")
            mapping = block_inst[b][1] # due to result from liveness analysis
            for x in mapping.keys():
                match(x):
                        case Instr(str, [arg1, arg2]):
                                if type(arg2) != Immediate:
                                    graph.add_vertex(arg2) #create a vertex for all W(k) to be coloured
                        case Instr('negq', [arg1]):
                                if type(arg1) != Immediate:
                                    graph.add_vertex(arg1)
                        case Instr('xorq', [arg1]):
                                if type(arg1) != Immediate:
                                    graph.add_vertex(arg1)
                        
                if self.isCallqInstr(x):   #Ignoring this as we don't have any callq or jumps in our logic now (Assgnt-2)
                        # print("Assigninh caller save registers to variables - ", mapping[x])
                        graph = self.AddEdgesToRegisters(mapping[x], graph)
                else: 
                        for y in mapping[x]:
                         #    print("Mapping for Instr: ",x, " for variables - ", y,  "\n")
                            match(x):
                                case Instr('movq', [arg1, arg2]):
                                    if y!= arg1 and y!=arg2 and type(arg2) != Immediate:
                                        #     print("Adding edge for -", y, " and ", arg2)
                                            graph.add_edge(y, arg2)
                                case Instr('addq', [arg1, arg2]):
                                    if y != arg2 and type(arg2) != Immediate:
                                        graph.add_edge(y, arg2)
                                case Instr('subq', [arg1, arg2]):
                                    if y != arg2 and type(arg2) != Immediate:
                                        graph.add_edge(y, arg2)
                                case Instr('negq', [arg1]):
                                    if y != arg1 and type(arg1) != Immediate:
                                            graph.add_edge(y, arg1)
                                case Instr('xorq', [arg1]):
                                    if y != arg1 and type(arg1) != Immediate:
                                            graph.add_edge(y, arg1)
                                case Instr('cmpq', [arg1, arg2]):
                                    if y!= arg1 and type(arg1) != Immediate:
                                        #     print("Adding edge for -", y, " and ", arg1)
                                            graph.add_edge(y, arg1)
                                    if y!=arg2 and type(arg2) != Immediate:
                                        #     print("Adding edge for -", y, " and ", arg2)
                                            graph.add_edge(y, arg2)
                                case Callq("collect", 0):   #all the call-live variables should have edge to callee-save registers
                                      if type(y) == Variable and y.var_types == TupleType:
                                           graph = self.AddEdgesToCalleeRegisters(y, graph)
                                           
     #     print("-------------END INTERFERENCE--------------------------------------------")
         return graph
    
    def precolour_registers(self, graph:UndirectedAdjList, sat: dict, pq: PriorityQueue) -> dict:
         vert = graph.vertices()
         reg = {}
         registers = {Reg("rax"): -1, Reg("rsp"): -2, Reg("rbp"): -3, Reg("r11"): -4, Reg("r15"): -5, Reg("rcx"): 0, Reg("rdx"): 1, Reg("rsi"): 2, Reg("rdi"): 3, Reg("r8"): 4, Reg("r9"): 5,
                      Reg("r10"): 6, Reg("rbx"): 7, Reg("r12"): 8, Reg("r13"): 9, Reg("r14"): 10 }
         for v in vert:
              if type(v) == Reg and v in registers.keys():
                    reg[v] = registers[v]
                    for adj in graph.adjacent(v):
                        sat[adj].append(registers[v])
                        if type(adj) == Reg:
                                continue
                        pq.increase_key(adj)
                    if registers[v] in self.callee_save and registers[v] not in self.used_callee:
                         self.used_callee.append(registers[v])  #increment the count of used callee save registers 
                   
         return reg, sat

    def color_graph(self, graph:UndirectedAdjList, move_graph:UndirectedAdjList ) -> dict:
         vert = graph.vertices()
     #     print("Graph Vertices:", vert)
         sat = {}
         color_v = {}
         precoloured_registers = {Reg("rax"): -1, Reg("rsp"): -2, Reg("rbp"): -3, Reg("r11"): -4, Reg("r15"): -5, Reg("al"): -1, Reg("ah"): -1}
         registers_list = ["rsp", "rbp", "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "al", "ah"]
         def compare(u,v):
            u = u.__repr__().split("@")[0]
            if u[1:] in registers_list:
                 u = Reg(u[1:])
            else:
                 u = Variable(u)
            v = v.__repr__().split("@")[0]
            if v[1:] in registers_list:
                 v = Reg(v[1:])
            else:
                 v = Variable(v)
            # print("comparing the lengths of sat of u-",u," and v-",v)
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
              sat[v] = []
         for v in vert:
            pq.push(v)
         
         color_v, sat = self.precolour_registers(graph, sat, pq)
        #  print("After pre-colouring - ", color_v ," Sat list-", sat)
         while not pq.empty():
              v = pq.pop()
              if type(v) == Reg:
                   continue
              min_val = float("inf")
              for x in move_graph.adjacent(v):
                   if x in color_v.keys() and color_v[x] not in sat[v] and color_v[x] >= 0:
                        min_val = color_v[x] #assign a color that is available from the move instructions 
                        break
              if min_val == float("inf"):
                for x in range(0,MAX_REG):
                    if x not in sat[v]:
                            min_val = x
                            break
              color_v[v] = min_val
              for adj in graph.adjacent(v):
                   if adj in precoloured_registers.keys():
                        continue
                   sat[adj].append(min_val)
                   pq.increase_key(adj)
         return color_v
    
    def assign_registers(self, color_v:dict) -> dict:
         registers = {0:Reg("rcx"), 1:Reg("rdx"), 2:Reg("rsi"), 3:Reg("rdi"), 4:Reg("r8"), 5:Reg("r9"),
                      6: Reg("r10"), 7: Reg("rbx"), 8:Reg("r12"), 9:Reg("r13"), 10:Reg("r14"), -1:Reg("rax"), -2:Reg("rsp"), -3: Reg("rbp")} # removed -4: Reg("r11"), -5:Reg("r15") {TUPLES}
         colors_mem = {}
         reg_var = {}
         dref_counter = -8 * len(self.used_callee) # should be placed below the callee saved registers. 
         for var in color_v.keys():
              if color_v[var] in registers.keys():
                reg_var[var] = registers[color_v[var]]
                if registers[color_v[var]] in self.callee_save and registers[color_v[var]] not in self.used_callee:
                     self.used_callee.append(registers[color_v[var]])
              elif color_v[var] in colors_mem.keys():
                     reg_var[var] = colors_mem[color_v[var]]
              else:
                     dref_counter = dref_counter - 8
                     reg_var[var] = Deref("rbp", dref_counter)
                     colors_mem[color_v[var]] = Deref("rbp", dref_counter)
                     if type(var) == Variable and var.var_types == TupleType:
                          self.root_stack = self.root_stack + 1 # count of spilled tuples
                     else:
                          self.stack_space = self.stack_space + 1 #count of stack variables
                
         return reg_var
                       

    def assign_homes_instrs(self, blocks, cfg: DirectedAdjList,
                            home: Dict[Variable, arg]) -> List[instr]:
        live_before = {}
        move_grph_blocks = {}
        live_block = {}
        move_graph = UndirectedAdjList()
        liveness_analyze = self.analyze_dataflow([], blocks, transpose(cfg))
        for x in blocks:
            if x == 'conclusion':
                 continue
            ss = blocks[x]
            move_graph = self.build_move_biase(move_graph, ss)
            move_grph_blocks[x] = move_graph
        graph = self.build_interference(liveness_analyze)
        color = self.color_graph(graph, move_graph)
        registers = self.assign_registers(color)
        block_result = {}
        for x in blocks:
             if x == 'conclusion':
                  continue
             res = []
             ss = blocks[x]
             for s in ss:
                temp = self.assign_homes_instr(s, registers)
                res.append(temp)
             block_result[x] = res
        return block_result
    

    def assign_homes(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                cfg = self.generate_CFG(body)
               #  body = self.remove_unused_blocks(body, cfg)
                new_cfg = self.generate_CFG(body)
                cfg_transpose = transpose(new_cfg)
                res = self.assign_homes_instrs(body, cfg, {})
                return X86Program(res)
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
                            res.append(Inst('movzbq', [arg1, byteRegister[arg2]]))
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
            case _:
                  res.append(i)   
        return res    

    def patch_instrs(self, blocks) -> List[instr]:
        block_result = {}
        for x in blocks.keys():
            if x == 'conclusion':
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

    def patch_instructions(self, p: X86Program) -> X86Program:
       match p:
            case X86Program(body):
                res = self.patch_instrs(body)
                return X86Program(res)
            case _:
                raise Exception('error in patch_instructions, unexpected ' + repr(p))        

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # print("Used Calle Count:", self.used_callee, " Stack Space:", self.stack_space)
        align_count = 8 * len(self.used_callee) + 8 * self.stack_space
        align_count = align(align_count,16)
        final_count = align_count - (8 * len(self.used_callee))
        res = {}
        # --------- PRELUDE
        main_inst = []
        main_inst.append(Instr('pushq', [Reg("rbp")]))
        main_inst.append(Instr("movq",[Reg("rsp"),Reg("rbp")]))
        for x in self.used_callee:
             main_inst.append(Instr('pushq', [x])) # push the callee save registers to stacks, pushq inst will automatically adjust to stack memory
        main_inst.append(Instr("subq", [Immediate(final_count), Reg("rsp")]))
        main_inst.append(Instr("movq", [Immediate(65536), Reg("rdi")]))
        main_inst.append(Instr("movq", [Immediate(16), Reg("rsi")]))
        main_inst.append(Callq('initialize',0))
        main_inst.append(Instr("movq", ["rootstack_begin(\%rip)", Reg("r15")]))
        main_inst.append(Instr("movq", [Immediate(0), Deref('r15',0)]))
        main_inst.append(Instr("addq", [Immediate(8*self.root_stack), Reg('r15')]))
        main_inst.append(Jump("start"))
        res[label_name('main')] = main_inst
        # --------- PROGRAM
        for block in p.body.keys():
             res[block] = p.body[block]
        # CONCLUDE
        conlude_inst = []
        conlude_inst.append(Instr("subq", [Immediate(8*self.root_stack), Reg("r15")]))
        conlude_inst.append(Instr("addq", [Immediate(final_count), Reg("rsp")]))
        for x in self.used_callee:
             conlude_inst.append(Instr('popq', [x])) # pop the callee save registers from memory
        conlude_inst.append(Instr('popq', [Reg("rbp")]))
        conlude_inst.append(Instr('retq', []))
        res[label_name('conclusion')] = conlude_inst
        return  X86Program(res)   
    
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
                    print("Compare Inst:", e)
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
            case Assign([Subscript(tup, index)], value):
                  tup_exp = self.pe_exp(tup)
                  ind_exp = self.pe_exp(index)
                  val = self.pe_exp(value)
                  return Assign([Subscript(tup_exp, ind_exp)], val)
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