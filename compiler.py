import ast
from ast import *
from graph import UndirectedAdjList
from priority_queue import PriorityQueue
from utils import * 
from x86_ast import *
import os
import copy
from typing import List, Tuple, Set, Dict


Binding = Tuple[Name, expr]
Temporaries = List[Binding]
MAX_REG = 100

class Compiler:
    
    stack_space = 0
    used_callee = []
    callee_save = [Reg("rsp"), Reg("rbp"), Reg("rbx"), Reg("r12"), Reg("r13"), Reg("r14"), Reg("15")]
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
                pe_module = self.pe_P(p)
                # print("received pe code:",pe_module.body)
                res = self.interp_stmts(pe_module.body, [])
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

    # def assign_homes_arg_old(self, a: arg, home: Dict[Variable, arg]) -> arg:
    #     match a:
    #         case Immediate(value):
    #             return Immediate(value)
    #         case Variable(id):
    #             if id in home.keys():
    #                  return home[id]   
    #             self.stack_space = self.stack_space - 8
    #             reg_mem = Deref("rbp",self.stack_space)
    #             home[id] = reg_mem
    #             return reg_mem
    #         case Reg(id):
    #             return Reg(id)
    #         case _:
    #             raise Exception('error in assign_homes_arg, unexpected ' + repr(a))       

    # def assign_homes_instr_old(self, i: instr,
    #                        home: Dict[Variable, arg]) -> instr:
    #     match(i):
    #         case Instr('movq', [arg1, arg2]):
    #                 arg1_stmt = self.assign_homes_arg(arg1, home)
    #                 arg2_stmt = self.assign_homes_arg(arg2, home)
    #                 inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
    #                 return inst_stmt
    #         case Instr('addq', [arg1, arg2]):
    #                 arg1_stmt = self.assign_homes_arg(arg1, home)
    #                 arg2_stmt = self.assign_homes_arg(arg2, home)
    #                 inst_stmt = Instr('addq', [arg1_stmt, arg2_stmt])
    #                 return inst_stmt
    #         case Instr('subq', [arg1, arg2]):
    #                 arg1_stmt = self.assign_homes_arg(arg1, home)
    #                 arg2_stmt = self.assign_homes_arg(arg2, home)
    #                 inst_stmt = Instr('movq', [arg1_stmt, arg2_stmt])
    #                 return inst_stmt
    #         case Instr('negq', [arg1]):
    #                 arg1_stmt = self.assign_homes_arg(arg1, home)
    #                 inst_stmt = Instr('negq', [arg1_stmt])
    #                 return inst_stmt
    #         case Callq("read_int",0):
    #                 return i
    #         case Callq("print_int", 0):
    #                 return i
    #         case _:
    #             raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
     

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
            case Callq("read_int",0):
                    return i
            case Callq("print_int", 0):
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
            case Callq("read_int",0):
                   w_var = self.live_arg(Reg("rax"))
                   if w_var != None:
                        res.add(w_var)
            case Callq("print_int", 0):
                   return None
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
            case Callq("read_int",0):
                   return None
            case Callq("print_int", 0):
                   w_var = self.live_arg(Reg("rdi"))
                   if w_var != None:
                        res.add(w_var)
            case _:
                raise Exception('error in assign_homes_instr, unexpected ' + repr(i))
         return res


    def uncover_live(self, ss: List[instr]) -> dict:
         live_dict = {}
         live_var = set()
         for x in range(len(ss)-1,-1,-1):
            i = ss[x]
            r_vars = self.R_function(i)
            w_vars = self.W_function(i)
            # print("for instr-", i, " read are-", r_vars, " | write are- ",w_vars)
            # print("live variables before - ", live_var)
            if w_vars != None:
                for d in w_vars:
                    live_var.discard(d)
            if r_vars != None:
                live_var.update(r_vars)
            # print("live variables after - ", live_var)
            if x != 0:
                live_dict[ss[x-1]] = live_var.copy()
         live_dict[ss[len(ss)-1]] = set()
         return live_dict
    
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
         regs = ["rax", "rbp", "rbx", "r12", "r13", "r14", "r15"]
         print("Adding set-",vars, " to callee registers")
         for x in vars:
              for r in regs:
                   if x != Reg(r):
                    graph.add_edge(x, Reg(r))
         return graph
    
    def build_move_biase(self, ss: List[instr]) -> UndirectedAdjList:
         graph = UndirectedAdjList()
         for s in ss:
            match(s):
                case Instr('movq', [arg1, arg2]):
                        if type(arg1) != Immediate and type(arg2) != Immediate:
                            graph.add_edge(arg1, arg2)
                case _:
                    continue
         return graph       
                
    
    def build_interference(self, mapping: dict) -> UndirectedAdjList:
         graph = UndirectedAdjList()
         for x in mapping.keys():
            #    if self.isCallqInstr(x):   #Ignoring this as we don't have any callq or jumps in our logic now (Assgnt-2)
            #         graph = self.AddEdgesToRegisters(mapping[x], graph)
            #    else:
                    if len(mapping[x]) == 0:
                         match(x):
                            case Instr(str, [arg1, arg2]):
                                    graph.add_vertex(arg1)
                                    graph.add_vertex(arg2)
                            case Instr('negq', [arg1]):
                                    graph.add_vertex(arg1)
                    else:     
                        for y in mapping[x]:
                            print("Mapping for Instr: ",x, " for variables - ", y)
                            match(x):
                                case Instr('movq', [arg1, arg2]):
                                    if y!= arg1 and y!=arg2:
                                            graph.add_edge(y, arg2)
                                    elif y!= arg1:
                                            graph.add_edge(y,arg2)
                                case Instr('addq', [arg1, arg2]):
                                    if y != arg2:
                                        graph.add_edge(y, arg2)
                                case Instr('subq', [arg1, arg2]):
                                    if y != arg2:
                                        graph.add_edge(y, arg2)
                                case Instr('negq', [arg1]):
                                    if y != arg1:
                                            graph.add_edge(y, arg1)
         return graph
    
    def precolour_registers(self, graph:UndirectedAdjList, sat: dict, pq: PriorityQueue) -> dict:
         vert = graph.vertices()
         reg = {}
         registers = {Reg("rax"): -1, Reg("rsp"): -2, Reg("rbp"): -3, Reg("r11"): -4, Reg("r15"): -5}
         for v in vert:
              if type(v) == Reg and v in registers.keys():
                    reg[v] = registers[v]
                    for adj in graph.adjacent(v):
                        sat[adj].append(registers[v])
                        if type(adj) == Reg:
                                continue
                        pq.increase_key(adj)
                    if registers[v] in self.callee_save:
                         self.used_callee.append(registers[v])  #increment the count of used callee save registers 
                   
         return reg, sat

    def color_graph(self, graph:UndirectedAdjList, move_graph:UndirectedAdjList ) -> dict:
         vert = graph.vertices()
         sat = {}
         color_v = {}
         def compare(u,v):
            u = u.__repr__().split("@")[0]
            if u == "rax" or u == "rbi":
                 u = Reg(u)
            else:
                 u = Variable(u)
            v = v.__repr__().split("@")[0]
            if v == "rax" or v == "rbi":
                 v = Reg(v)
            else:
                 v = Variable(v)
            # print("comparing the lengths of sat of u-",u," and v-",v)
            if  len(sat[u]) == len(sat[v]):
                 u_colours = []
                 v_colours = []
                 for x in move_graph.adjacent(u):
                      if x in color_v.keys() and color_v[x] not in sat[u]:
                           u_colours.append(color_v[x])
                 for x in move_graph.adjacent(v):
                      if x in color_v.keys() and color_v[x] not in sat[v]:
                           v_colours.append(color_v[x])
                 return len(u_colours) < len(v_colours)
                           
            else:
                 return  len(sat[u]) < len(sat[v])
         pq = PriorityQueue(compare)
         for v in vert:
              sat[v] = []
         for v in vert:
            if type(v) == Reg:
              continue
            pq.push(v)
         
         color_v, sat = self.precolour_registers(graph, sat, pq)
         while not pq.empty():
              v = pq.pop()
              min_val = float("inf")
              for x in move_graph.adjacent(v):
                   if x in color_v.keys() and color_v[x] not in sat[v]:
                        min_val = color_v[x] #assign a color that is available from the move instructions 
                        break
              if min_val == float("inf"):
                for x in range(0,MAX_REG):
                    if x not in sat[v]:
                            min_val = x
                            break
            #   print("Minimum value gen for vertex v-",v," is:", min_val)
              color_v[v] = min_val
              for adj in graph.adjacent(v):
                   sat[adj].append(min_val)
                   pq.increase_key(adj)
                #    print("added min_Val:",min_val," to the saturation list of edge:",adj)
         return color_v
    
    def assign_registers(self, color_v:dict) -> dict:
         registers = {0:Reg("rcx"), 1:Reg("rdx"), 2:Reg("rsi"), 3:Reg("rdi"), 4:Reg("r8"), 5:Reg("r9"),
                      6: Reg("r10"), 7: Reg("rbx"), 8:Reg("r12"), 9:Reg("r13"), 10:Reg("r14"), -1:Reg("rax"), -2:Reg("rsp"), -3: Reg("rbp"), -4: Reg("r11"), -5:Reg("r15")}
         reg_var = {}
         dref_counter = -8 * len(self.used_callee) # should be placed below the callee saved registers. 
         for var in color_v.keys():
              if color_v[var] in registers.keys():
                reg_var[var] = registers[color_v[var]]
                if registers[color_v[var]] in self.callee_save:
                     self.used_callee.append(registers[color_v[var]])
              else:
                dref_counter = dref_counter - 8
                reg_var[var] = Deref("rbp", dref_counter)
                self.stack_space = self.stack_space + 1 #count of stack variables
                
         return reg_var
                       

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[Variable, arg]) -> List[instr]:
        res = []
        dict = self.uncover_live(ss)
        move_graph = self.build_move_biase(ss)
        print("-----uncover-live-------")
        for i in dict.keys():
             print(i," after varibales- ", dict[i])
        # print("--------------Move Grpah----------------")
        # print(move_graph.show())
        graph = self.build_interference(dict)
        print(graph.show())
        color = self.color_graph(graph, move_graph)
        print("\ncolor mapping:", color)
        registers = self.assign_registers(color)
        print("\nassign registers pass o/p-", registers)
        for s in ss:
            temp = self.assign_homes_instr(s, registers)
            res.append(temp)
        # print("\nAssign Homes result:",res)
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
        align_count = 8 * len(self.used_callee) + 8 * self.stack_space
        if align_count % 16 != 0 :
             align_count = align_count + 8 # forcing it to be a factor of 16
        final_count = align_count - (8 * len(self.used_callee))
        res = []
        # --------- PRELUDE
        res.append(Instr('pushq', [Reg("rbp")]))
        res.append(Instr("movq",[Reg("rsp"),Reg("rbp")]))
        for x in self.used_callee:
             res.append(Instr('pushq', [x])) # push the callee save registers to stacks, pushq inst will automatically adjust to stack memory
        res.append(Instr("subq", [Immediate(final_count), Reg("rsp")]))
        # --------- PROGRAM
        for y in p.body:
             res.append(y)
        # CONCLUDE
        res.append(Instr("addq", [Immediate(final_count), Reg("rsp")]))
        for x in self.used_callee:
             res.append(Instr('popq', [x])) # pop the callee save registers from memory
        res.append(Instr('popq', [Reg("rbp")]))
        res.append(Instr('retq', []))
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
                   
      
    ############################################################################
    # Challenge - Ex-4.7 Move Biasing
    ############################################################################