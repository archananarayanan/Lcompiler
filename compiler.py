import ast
from ast import *
from utils import * 
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict


Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:
    
    stack_space = 0
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
            case _:
                raise Exception('error in rco_stmt, unexpected ' + repr(s))
        
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
                res = self.interp_stmts(body, [])
                return Module(res)
            case _:
                raise Exception('error in remove_complex_operands, unexpected ' + repr(p))
        

    ############################################################################
    # Select Instructions
    ############################################################################

    def select_arg(self, e: expr) -> arg:
            match e:
                case Constant(value):
                    return Immediate(value)
                case Name(id):
                    return Variable(id)
                case Reg(id):
                    return Reg(id)
                case _:
                    raise Exception('error in select_arg, unexpected ' + repr(e))

    def parse_Binary(self, e:expr) -> List[arg]:
        res = []
        match e:
            case Expr(BinOp(left, Add(), right)):
                    left = self.select_arg(left)
                    right = self.select_arg(right)
                    res.append(left)
                    res.append(right)
            case Expr(BinOp(left, Sub(), right)):
                    left = self.select_arg(left)
                    right = self.select_arg(right)
                    res.append(left)
                    res.append(right)

        return res       


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
            case Expr(BinOp(left, Add(), right)):
                l = self.select_arg(left)
                r = self.select_arg(right)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('addq', [r, Reg("rax")]))
            case Expr(BinOp(left, Sub(), right)):
                l = self.select_arg(left)
                r = self.select_arg(right)
                res.append(Instr('movq', [l, Reg("rax")]))
                res.append(Instr('subq', [r, Reg("rax")]))
            case Expr(UnaryOp(USub(), v)):
                val = self.select_arg(v)
                neg_stmt = Instr('negq', [val])
                res.append(neg_stmt)
            case Expr(Call(Name('input_int'), [])):
                call_stmt = Callq("read_int",0)
                res.append(call_stmt)
            case Assign([Name(id)], value):
                assign_stmt = self.handle_assign(value, Variable(id))
                for x in assign_stmt[1]:
                    res.append(x)
            case _:
                raise Exception('error in select_stmt, unexpected ' + repr(s))  
            
        return res
    
    def handle_assign(self, s: stmt, id: any):
         res = [] 
         match s:
            case Call(Name('print'), [arg]):
                res = []
            case BinOp(left, Add(), right):
                l,inst_l = self.handle_assign(left,id)
                r,inst_r = self.handle_assign(right,id)
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
                    l,inst_l = self.handle_assign(left,id)
                    r,inst_r = self.handle_assign(right,id)
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
                    val,inst = self.handle_assign(v,id)
                    for x in inst:
                     res.append(x)
                    neg_stmt = Instr('negq', [val])
                    res.append(Instr('movq', [val, id]))
                    res.append(neg_stmt)
                    return id, res
            case Call(Name('input_int'), []):
                    inst_stmt = Instr('movq', [Reg("rax"),id])
                    call_stmt = Callq("read_int",0)
                    res.append(call_stmt)
                    if id != None:
                         res.append(inst_stmt)
                    return Reg("rax"),res
            case _:
                   arg = self.select_arg(s)
                   inst_stmt = Instr('movq', [arg, id])
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
            case Module(body):
                res = self.select_interp_stmts(body, [])
                return X86Program(res)
            case _:
                raise Exception('error in select_instructions, unexpected ' + repr(p))      

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        match a:
            case Immediate(value):
                return Immediate(value)
            case Variable(id):
                if id in home.keys():
                     return home[id]   
                self.stack_space = self.stack_space - 8
                reg_mem = Deref("rbp",self.stack_space)
                home[id] = reg_mem
                return reg_mem
            case Reg(id):
                return Reg(id)
            case _:
                raise Exception('error in assign_homes_arg, unexpected ' + repr(a))       

    def assign_homes_instr(self, i: instr,
                           home: Dict[Variable, arg]) -> instr:
        match(i):
            case Instr('movq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, home)
                    arg2_stmt = self.assign_homes_arg(arg2, home)
                    inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('addq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, home)
                    arg2_stmt = self.assign_homes_arg(arg2, home)
                    inst_stmt = Instr('addq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('subq', [arg1, arg2]):
                    arg1_stmt = self.assign_homes_arg(arg1, home)
                    arg2_stmt = self.assign_homes_arg(arg2, home)
                    inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
                    return inst_stmt
            case Instr('negq', [arg1]):
                    arg1_stmt = self.assign_homes_arg(arg1, home)
                    inst_stmt = Instr('negq', [arg1_stmt])
                    return inst_stmt
            case Callq("read_int",0):
                    return i
            case Callq("print_int", 0):
                    return i
            case _:
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        res = []
        for s in ss:
            temp = self.assign_homes_instr(s, home)
            res.append(temp)
        return res

    def assign_homes(self, p: X86Program) -> X86Program:
        match p:
            case X86Program(body):
                res = self.assign_homes_instrs(body, {})
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
            case _:
                  res.append(i)   
        return res    

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        res = []
        for s in ss:
            temp = self.patch_instr(s)
            for x in temp:
                 res.append(x)
        return res        

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
        if self.stack_space % 16 != 0 :
             self.stack_space = self.stack_space - 8 # forcing it to be a factor of 16
        self.stack_space = self.stack_space * -1
        res = []
        # --------- PRELUDE
        res.append(Instr('pushq', [Reg("rbp")]))
        res.append(Instr("movq",[Reg("rsp"),Reg("rbp")]))
        res.append(Instr("subq", [Immediate(self.stack_space), Reg("rsp")]))
        # --------- PROGRAM
        for y in p.body:
             res.append(y)
        # CONCLUDE
        res.append(Instr("addq", [Immediate(self.stack_space), Reg("rsp")]))
        res.append(Instr('popq', [Reg("rbp")]))
        res.append(Instr('retq', []))
        return  X86Program(res)   
    
    ############################################################################
    # Challenge - Ex-2.7 Partial Evaluators
    ############################################################################

    def pe_neg(self, r: expr):
         match r:
              case Constant(n):
                   return Constant(neg64(n))
              case _:
                   return UnaryOp(USub(), r)
            
    def pe_add(self, r1:expr, r2:expr):
         match(r1,r2):
              case (Constant(n1), Constant(n2)):
                   return Constant(add64(n1,n2))
              case _:
                   return BinOp(r1, Add(), r2)
    
    def pe_sub(self, r1:expr, r2:expr):
         match(r1,r2):
              case (Constant(n1), Constant(n2)):
                   return Constant(sub64(n1,n2))
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
                     pe = self.pe_neg(left,right)
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
                    raise Exception('error in pe_exp, unexpected ' + repr(e))

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
            case _:
                raise Exception('error in pe_stmt, unexpected ' + repr(s))
             
    def pe_P(self, p: Module) -> Module:
         match p:
              case Module(body):
                   new_body = [self.pe_stmt(s) for s in body]
                   return Module(new_body)
              case _:
                   raise Exception('error in  pe_P, unexpected ' + repr(p))
                   
     
