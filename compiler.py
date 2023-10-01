import ast
from ast import *
from graph import *
from priority_queue import PriorityQueue
from utils import * 
from x86_ast import *
import os
import copy
from typing import List, Tuple, Set, Dict


Binding = Tuple[Name, expr]
Temporaries = List[Binding]
MAX_REG = 100
f = open("out.txt", "w")

class Compiler:
    
    stack_space = 0
    used_callee = []
    callee_save = [Reg("rsp"), Reg("rbp"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"), Reg("15")]
    

    ############################################################################
    # Shrink the Lif 
    ############################################################################
    
    def shrink(self, s: expr) -> expr:
          print("Received Shrink exp:", s)
          match s:
                case IfExp(test, body, orelse):
                    res = self.shrink(test)
                    body_exp = []
                    for b in body:
                        body_exp.append(self.shrink(b))
                    or_exp = []
                    for o in orelse:
                        or_exp.append(self.shrink(o))
                    return IfExp(res, body_exp, or_exp)
                case BoolOp(And(), values):
                    left = values[0]; right = values[1]
                    return IfExp(left, right, Constant(False))
                case BoolOp(Or(), values):
                    left = values[0]; right = values[1]
                    return IfExp(left, Constant(True), right)
                case _:
                    return s
               
    def shrink_stmt(self, s: stmt) -> stmt:
        match s:
            case If(test, body, orelse):
                print("Received IF Shrink stmt:", s)
                res = self.shrink(test)
                body_exp = []
                for b in body:
                     body_exp.append(self.shrink_stmt(b))
                or_exp = []
                for o in orelse:
                     or_exp.append(self.shrink_stmt(o))
                return If(res, body_exp, or_exp)
            case _:
                print("Received Shrink stmt:", s)
                return s
              

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:
         if not need_atomic:
             return (e, [])
         else:
            match e:
                case BinOp(left, Add(), right):
                    l = self.rco_exp(left, True)
                    r = self.rco_exp(right, True)
                    var = generate_name("temp")
                    temp = l[1]
                    for y in r[1]:
                        temp.append(y)
                    temp.append((Name(var), BinOp(l[0] , Add(), r[0])))
                    return (Name(var), temp)
                case BinOp(left, Sub(), right):
                    l = self.rco_exp(left, True)
                    r = self.rco_exp(right, True)
                    var = generate_name("temp")
                    temp = l[1]
                    for y in r[1]:
                        temp.append(y)
                    temp.append((Name(var),BinOp(l[0] , Sub(), r[0])))
                    return (Name(var), temp)
                case UnaryOp(USub(), v):
                    val = self.rco_exp(v, True)
                    var = generate_name("temp")
                    val[1].append((Name(var), UnaryOp(USub(), val[0])))
                    return (Name(var), val[1])
                case IfExp(test, body, orelse):
                    test_exp = self.rco_exp(test, True)
                    body_exp = self.rco_exp(body, True)
                    or_exp = self.rco_exp(orelse, True)
                    temp = []
                    b_temp = []
                    o_temp = []
                    for x in test_exp[1]:
                        temp.append(test_exp[1])
                    for x in body_exp[1]:
                        b_temp.append(Assign([x[0]],x[1]))
                    body1 = Begin(b_temp, body_exp[0])
                    for x in or_exp[1]:
                        o_temp.append(Assign([x[0]],x[1]))
                    or1 = Begin(o_temp, or_exp[0])
                    print("Test-", test_exp[0])
                    print("Body-", body1)
                    print("Or-", or1)
                    return (IfExp(test_exp[0], body1, or1), temp)
                case UnaryOp(Not(), v):
                    val = self.rco_exp(v, True)
                    return (UnaryOp(Not(), val[0]), val[1])
                case Compare(left, [cmp], [right]):
                    print("Compare Inst:", e)
                    l = self.rco_exp(left, True)
                    r = []
                    temp = []
                    print("left-", left)
                    print("right-", right)
                    for x in l[1]:
                         temp.append(x)
                    r = self.rco_exp(right, True)
                    for x in r[1]:
                         temp.append(x)
                    return (Compare(l[0], [cmp], [r[0]]), temp)
                case Constant(value):
                    return (e, [])
                case Call(Name('input_int'), []):
                    return (e, [])
                case Name(id):
                    return (e, [])
                case _:
                    raise Exception('error in rco_exp, unexpected ' + repr(e))

    def rco_stmt(self, s: stmt) -> List[stmt]:
        res = []
        match s:
            case Expr(Call(Name('print'), [arg])):
                val = self.rco_exp(arg, True)
                for x in val[1]:
                    print(x)
                    res.append(Assign([x[0]],x[1]))
                print_stmt = Expr(Call(Name('print'), [val[0]])) 
                res.append(print_stmt)
            case Expr(value):
                val = self.rco_exp(value, True)
                for x in val[1]:
                    print(x)
                    res.append(Assign([x[0]],x[1]))
            case Assign([Name(id)], value):
                val = self.rco_exp(value, True)
                for x in val[1]:
                    print(x)
                    res.append(Assign([x[0]],x[1]))
                res.append(Assign([Name(id)], val[0]))
            case If(test, body, orelse):
                val = self.rco_exp(test, True)
                for x in val[1]:
                    print(x)
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
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        
        return res
    
    def interp_stmt(self, s, cont, stmts: List[stmt]) -> List[stmt]:
        sif = self.shrink_stmt(s)
        print("------- RESULT FROM SHRINK------------")
        print(sif)
        res = self.rco_stmt(sif)
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
                # print("received pe code:",pe_module.body)
                res = self.interp_stmts(pe_module.body, [])
                return Module(res)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))
        
    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, body, basic_blocks, name="block"):
         label = generate_name(name)
         basic_blocks[label_name(label)] = body
         return [Goto(label)], basic_blocks
    
    def explicate_effect(self, e: expr, cont, basic_blocks):
         match e:
              case IfExp(test, body, orelse):
                   body_b = self.explicate_effect(body, cont, basic_blocks)
                   or_b = self.explicate_effect(orelse, cont, basic_blocks)
                   ifexp = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return ifexp
              case Call(func, args):
                   stmts = [e] + cont
                   call_b, basic_blocks = self.create_block(stmts, basic_blocks)
                   return call_b
              case Begin(body, res):
                   goto_cont, basic_blocks = self.create_block(cont, basic_blocks)
                   cont_b = [Return(res)]+ goto_cont #doesnt make sense, have to verify. 
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
                   goto_cont, basic_blocks = self.create_block(cont, basic_blocks)
                   cont_b = [Assign([lhs], res)]+ goto_cont
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
                   body_b = self.explicate_pre(body, thn, els, basic_blocks)
                   or_b = self.explicate_pre(orelse, els, thn, basic_blocks)
                   test_b = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return test_b
              case Begin(body, result):
                   cont_b = self.explicate_pre(result, thn, els, basic_blocks)
                   for s in reversed(body):
                    cont_b = self.explicate_stmt(s, cont_b, basic_blocks)
                   return cont_b
              case _ :
                   goto_els, basic_blocks = self.create_block(els, basic_blocks)
                   goto_thn, basic_blocks = self.create_block(thn, basic_blocks)
                   return [If(Compare(cnd, [Eq()], [Constant(False)]), goto_thn , goto_els )]
              
    def explicate_stmt(self, s, cont, basic_blocks):
         match s:
              case Assign([lhs], rhs):
                   return self.explicate_assign(rhs, lhs, cont, basic_blocks)
              case Expr(value):
                   return self.explicate_effect(value, cont, basic_blocks)
              case If(test, body, orelse):
                   body_b = cont
                   for s1 in reversed(body):
                        body_b = self.explicate_stmt(s1, body_b, basic_blocks)
                   or_b = cont
                   for s1 in reversed(orelse):
                        or_b = self.explicate_stmt(s1, or_b, basic_blocks)
                   test_b = self.explicate_pre(test, body_b, or_b, basic_blocks)
                   return test_b
              case _:
                   return [s] + cont
              
    def explicate_control(self, p):
         match p:
              case Module(body):
                   new_body = [Return(Constant(0))]
                   basic_blocks = {}
                   print("-------------------Program Body---------------------")
                   print(body)
                   for s in reversed(body):
                        print("Compiling stmt-", s)
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
                return 'lt'
            case LtE():
                return 'lte'
            case Gt():
                return 'gt'
            case GtE():
                return 'gte'
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
            case _:
                var = self.select_arg(e)
         return var,res
                   

    def select_stmt(self, s: stmt) -> List[instr]:
        res = []
        match s:
            case Call(Name('print'), [arg]):
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
                cmp_stmt = Instr('cmpq', [left_arg[0], right_arg[0]])
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
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))  
            
        return res
    
    def handle_assign(self, s: stmt, id: any):
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
                   cmp_stmt = Instr('cmpq', [left, right])
                   cmp_op = self.cmp_instr(cmp)
                   set_inst = Instr('set'+cmp_op, [Reg("al")])
                   mov_inst = Instr('movzbq',[Reg("al"), id])
                   res.append(cmp_stmt)
                   res.append(set_inst)
                   res.append(mov_inst)
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
                print("left:",l," right:", r," l_inst:", inst_l," r_inst:", inst_r)
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
                res.append(Instr('addq', [r, Reg("rax")]))
                return res,Reg("rax")
            case UnaryOp(USub(), v):
                inst,val = self.handle_print(v)
                for x in inst:
                     res.append(x)
                res.append(Instr('movq', [val, Reg("rax")]))
                res.append(Instr('negq', Reg("rax")))
                return res,Reg("rax")
            case Call(Name('input_int'), []):
                call_stmt = Callq("read_int",0)
                res.append(call_stmt)
                return res,Reg("rax")
            case Compare(left, [cmp], [right]):
                   cmp_stmt = Instr('cmpq', [left, right])
                   cmp_op = self.cmp_instr(cmp)
                   set_inst = Instr('set'+cmp_op, [Reg("al")])
                   mov_inst = Instr('movzbq',[Reg("al"), Reg("rax")])
                   res.append(cmp_stmt)
                   res.append(set_inst)
                   res.append(mov_inst)
                   return res, Reg("rax")
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
         sorted_cfg = topological_sort(graph)
         new_body = {}
         in_edges_blocks = {}
         for x in sorted_cfg:
              if x == 'conclusion':
                   continue
              in_edges = graph.ins[x]
              print("In Edges of block-",x," are-", in_edges)
              if len(in_edges) == 1:
                   in_edges_blocks[in_edges[0]] = x
         print("In Edges Blocks are-", in_edges_blocks)
         for x in sorted_cfg:
              if x == 'conclusion':
                   continue
              if x in in_edges_blocks.values() and x not in in_edges_blocks.keys():
                   continue
              
              new_body[x] = []
              if x in in_edges_blocks.keys():
                   for inst in body[x]:
                        print("Compiling Inst-", inst, " for block-", x, "with in-edge as:", in_edges_blocks[x])
                        if type(inst) == Jump and inst.label == in_edges_blocks[x]:
                             print("matched with the jump inst")
                             if in_edges_blocks[x] in new_body.keys():
                                for add_inst in new_body[in_edges_blocks[x]]:
                                  new_body[x].append(add_inst)
                             else:
                                for add_inst in body[in_edges_blocks[x]]:
                                    new_body[x].append(add_inst)
                        else:
                             new_body[x].append(inst)
                        print("Final Inst set of the blcok-", new_body[x])
                        print("--------------------------------------------------------")
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
                    inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
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
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
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
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
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
         print(cfg.show())
         return cfg
                                            

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
        #  print("Block_inst keys:", block_inst.keys())
         for b in block_inst.keys():
            # print("Blovk insts-", block_inst[b])
            mapping = block_inst[b]
            for x in mapping.keys():
                match(x):
                        case Instr(str, [arg1, arg2]):
                                if type(arg2) != Immediate:
                                    graph.add_vertex(arg2) #create a vertex for all W(k) to be coloured
                        case Instr('negq', [arg1]):
                                if type(arg1) != Immediate:
                                    graph.add_vertex(arg1)
                        
                if self.isCallqInstr(x):   #Ignoring this as we don't have any callq or jumps in our logic now (Assgnt-2)
                        # print("Assigninh caller save registers to variables - ", mapping[x])
                        graph = self.AddEdgesToRegisters(mapping[x], graph)
                else: 
                        for y in mapping[x]:
                            # print("Mapping for Instr: ",x, " for variables - ", y)
                            match(x):
                                case Instr('movq', [arg1, arg2]):
                                    if y!= arg1 and y!=arg2 and type(arg2) != Immediate and type(arg1) != Immediate:
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
         print("Graph Vertices:", vert)
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
                      6: Reg("r10"), 7: Reg("rbx"), 8:Reg("r12"), 9:Reg("r13"), 10:Reg("r14"), -1:Reg("rax"), -2:Reg("rsp"), -3: Reg("rbp"), -4: Reg("r11"), -5:Reg("r15")}
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
                     self.stack_space = self.stack_space + 1 #count of stack variables
                
         return reg_var
                       

    def assign_homes_instrs(self, sorted_blocks, blocks, cfg: DirectedAdjList,
                            home: Dict[Variable, arg]) -> List[instr]:
        live_before = {}
        move_grph_blocks = {}
        live_block = {}
        move_graph = UndirectedAdjList()
        for x in sorted_blocks:
            if x == 'conclusion':
                 continue
            print("Addresing statements of block-", x)
            ss = blocks[x]
            self.uncover_live(ss, x, live_before, {}, live_block, cfg)
            move_graph = self.build_move_biase(move_graph, ss)
            print(dict)
            print("=============================================")
            print("Live Before for the Block- ", live_before[x])
            move_grph_blocks[x] = move_graph
            print("-----------------Block End---------------------------")
        print("Final Dictionary -------------------------")
        print(live_block)
        print(move_graph.show())
        print("-----------------------------------------------")
        graph = self.build_interference(live_block)
        print("Interference Graph-------------------")
        print(graph.show())
        color = self.color_graph(graph, move_graph)
        registers = self.assign_registers(color)
        print("Registers Coloured- ", registers)
        block_result = {}
        for x in sorted_blocks:
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
                print("Receied Homes ARGS-", body, "\n")
                cfg = self.generate_CFG(body)
                body = self.remove_unused_blocks(body, cfg)
                print("After removinf Unused Blocks-")
                print(body)
                print("------------------------------------------------")
                new_cfg = self.generate_CFG(body)
                cfg_transpose = transpose(new_cfg)
                sorted_cfg = topological_sort(cfg_transpose)
                print("Sorted CFG-", sorted_cfg)
                res = self.assign_homes_instrs(sorted_cfg, body, cfg, {})
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
                    if arg2 not in registers:
                         if arg2 in boolRegisters:
                            res = []
                            res.append(i)
                            res.append(Inst('movzbq', [arg1, byteRegister[arg2]]))
                    else:
                         res.append(i)
            case Instr('cmpq', [arg1, arg2]):
                  if type(arg1) == Deref and type(arg2) == Deref:
                         arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                         arg2_stmt = Instr('cmpq', [Reg("rax"), arg2])
                         res.append(arg1_stmt)
                         res.append(arg2_stmt) 
                  elif type(arg1) == Immediate and type(arg2) == Immediate:
                         arg1_stmt = Instr('movq', [arg1, Reg("rax")])
                         arg2_stmt = Instr('cmpq', [Reg("rax"), arg2])
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
            print("Accessing patch for block:", x)
            res = []
            ss = blocks[x]
            print("Set Of Inst:", ss)
            for s in ss:
                temp = self.patch_instr(s)
                for t in temp:
                    res.append(t)
            block_result[x] = res
            print("================== END BLOCK=====================")
        print("FInal Result:", block_result)
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
        main_inst.append(Jump("start"))
        res[label_name('main')] = main_inst
        # --------- PROGRAM
        for block in p.body.keys():
             res[block] = p.body[block]
        # CONCLUDE
        conlude_inst = []
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
                case Constant(value):
                    return (e)
                case Call(Name('input_int'), []):
                    return (e)
                case Name(id):
                    return (e)
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