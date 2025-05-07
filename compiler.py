from typing import Set, Dict, List, Tuple
import itertools
import sys
import traceback

from cs3020_support.python import *
import cs3020_support.x86 as x86
import constants
import cif
from interference_graph import InterferenceGraph
import print_x86defs


comparisons = ['eq', 'gt', 'gte', 'lt', 'lte']
gensym_num = 0
global_logging = True

tuple_var_types = {}
function_names = set()

def log(label, value):
    if global_logging:
        print()
        print(f'--------------------------------------------------')
        print(f'Logging: {label}')
        print(value)
        print(f'--------------------------------------------------')


def log_ast(label, value):
    log(label, print_ast(value))


def gensym(x):
    """
    Constructs a new variable name guaranteed to be unique.
    :param x: A "base" variable name (e.g. "x")
    :return: A unique variable name (e.g. "x_1")
    """

    global gensym_num
    gensym_num = gensym_num + 1
    return f'{x}_{gensym_num}'


##################################################
# typecheck
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr]) | Begin(Stmts, Expr)
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

TEnv = Dict[str, type]

@dataclass
class Callable:
    args: List[type]
    output_type: type

@dataclass 
class Any: 
    pass 

def typecheck(program: Program) -> Program:
    """
    Typechecks the input program; throws an error if the program is not well-typed.
    :param program: The Lfun program to typecheck
    :return: The program, if it is well-typed
    """

    prim_arg_types = {
        'add':   [int, int],
        'sub':   [int, int],
        'mult':  [int, int],
        'not': [bool],
        'or':  [bool, bool],
        'and':  [bool, bool],
        'gt':   [int, int],
        'gte':  [int, int],
        'lt':   [int, int],
        'lte':  [int, int],
    }

    prim_output_types = {
        'add':   int,
        'sub':   int,
        'mult':  int,
        'not': bool,
        'or':  bool,
        'and':  bool,
        'gt':   bool,
        'gte':  bool,
        'lt':   bool,
        'lte':  bool,
    }

    def tc_exp(e: Expr, env: TEnv) -> type:
        match e:
            case Call(func, args):
                arg_types = [tc_exp(a, env) for a in args]
                # returns Callable or raises its own error if not found/callable
                func_type = tc_exp(func, env)
                if isinstance(func_type, Callable): # check if it's callable
                    param_types = func_type.args
                    return_type = func_type.output_type
                    # assert len(param_types) == len(arg_types)
                    #we need the same number of parameters as arguements
                    for p, a in zip(param_types, arg_types):
                    #for every parameter and every argument in param_types and arg_types:
                        # type compatibility check allowing Any
                        assert p == a or p == Any or a == Any
                        #assert parameter type is the same as arguemtn type or,
                        #parameter is an 'Any' or,
                        #arguement is an 'Any'
                    # determine return type based on Any involvement
                    if Any not in arg_types:
                        return return_type
                    else:
                        return Any 
                else:
                    return Any 


            case Var(x):
                return env.get(x, Any)
            case Constant(i):
                if isinstance(i, bool):
                    return bool
                elif isinstance(i, int):
                    return int
                else:
                    return Any


            case Prim('eq', [e1, e2]):
                t1 = tc_exp(e1, env)
                t2 = tc_exp(e2, env)
                assert t1 == t2 or t1 == Any or t2 == Any 
                # basically here, if eq sees an "Any" type, we allow it but it will still return a bool
                return bool
                #even if its dynaically typed, comparing two things should always yeild a boolean so we dont need to change this


            case Begin(stmts, e1):
                tc_stmts(stmts, env)
                return tc_exp(e1, env)
            case Prim('tuple', args):
                arg_types = [tc_exp(a, env) for a in args]
                t = tuple(arg_types)
                return t
            case Prim('subscript', [e1, Constant(i)]):
                t = tc_exp(e1, env)
                if t == Any: 
                    return Any 
                elif isinstance(t, tuple):
                     # if index is invalid but no exception raised
                     if 0 <= i < len(t):
                         return t[i]
                     else:
                         return Any
                else:
                     return Any


            #The lovely primitive operation case
            case Prim(op, args):
                 if op in prim_arg_types: # check if op is in dicts before proceeding
                     arg_types = [tc_exp(a, env) for a in args]
                     expected_types = prim_arg_types[op]
                     #these are the expected types for whatever operation were doing ('add' would be [int, int])
                     # Assuming correct number of args
                     for at, et in zip(arg_types, expected_types):
                     #for argument type and expected type in arg_types and expected_types,
                        assert at == et or at == Any or et == Any
                        #assert argument type is the same as expected type, or
                        #argument type is an "Any", or,
                        #expected type is an "Any"
                     out_type = prim_output_types[op]
                     #finds expected return type. ('add' would be 'int')

                     if Any in arg_types: 
                        return Any 
                        #if any of the inputs are an 'Any' type (dynamic)
                        #the result will be an 'Any' type
                     else:
                        return out_type
                        #otherwise we maintain the static type (just like adding two 'int')
                 else:
                      return Any
            case _:
                return Any


    def tc_stmt(s: Stmt, env: TEnv):
        match s:
            case FunctionDef(name, params, body_stmts, return_type):
                function_names.add(name)
                arg_types = [t for x, t in params]
                env[name] = Callable(arg_types, return_type)
                new_env = env.copy()

                for x, t in params:
                    new_env[x] = t

                new_env['return value'] = return_type
                tc_stmts(body_stmts, new_env)

                for x in new_env:
                    if isinstance(new_env[x], tuple):
                        tuple_var_types[x] = new_env[x]

            case Return(e):
                 actual_type = tc_exp(e, env)
                 expected_type = env.get('return value', Any) # default to Any if not in func
                 assert expected_type == actual_type or expected_type == Any or actual_type == Any


            case While(condition, body_stmts):
                cond_type = tc_exp(condition, env)
                assert cond_type == bool or cond_type == Any
                tc_stmts(body_stmts, env)
            case If(condition, then_stmts, else_stmts):
                cond_type = tc_exp(condition, env)
                assert cond_type == bool or cond_type == Any
                tc_stmts(then_stmts, env)
                tc_stmts(else_stmts, env)
            case Print(e):
                exp_type = tc_exp(e, env)
                # tc_exp(e, env) 


            case Assign(x, e):
                t_e = tc_exp(e, env)
                # assert t_e == env[x] or t_e == Any or env[x] == Any
                env[x] = t_e
                if isinstance(t_e, tuple):
                     tuple_var_types[x] = t_e
            case _:
                pass


    def tc_stmts(stmts: List[Stmt], env: TEnv):
        for s in stmts:
            tc_stmt(s, env)

    match program:
        case Program(stmts):
            env = {}
            tc_stmts(stmts, env)

            for x in env:
                if isinstance(env[x], tuple):
                    tuple_var_types[x] = env[x]

            return program

##################################################
# remove-complex-opera*
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "tuple" | "subscript"
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Expr, Stmts)
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def rco(prog: Program) -> Program:
    """
    Removes complex operands. After this pass, the arguments to operators (unary and binary
    operators, and function calls like "print") will be atomic.
    :param prog: An Lfun program
    :return: An Lfun program with atomic operator arguments.
    """

    def rco_stmt(stmt: Stmt, new_stmts: List[Stmt]) -> Stmt:
        match stmt:
            case FunctionDef(name, params, body_stmts, return_type):
                return FunctionDef(name, params, rco_stmts(body_stmts), return_type)
            case Return(e):
                atomic_e = rco_exp(e, new_stmts) # assign result of rco_exp
                return Return(atomic_e) # use the atomic expression
            case Assign(x, e1):
                new_e1 = rco_exp(e1, new_stmts)
                return Assign(x, new_e1)
            case Print(e1):
                new_e1 = rco_exp(e1, new_stmts)
                return Print(new_e1)
            case If(condition, then_stmts, else_stmts):
                new_condition = rco_exp(condition, new_stmts)
                new_then_stmts = rco_stmts(then_stmts)
                new_else_stmts = rco_stmts(else_stmts)

                return If(new_condition,
                          new_then_stmts,
                          new_else_stmts)
            case While(condition, body_stmts):
                # EXPERIMENTAL RCO: Just atomize the initial condition expression.
                # explicate control must handle the loop structure and re-evaluation.
                new_condition = rco_exp(condition, new_stmts)
                new_body_stmts = rco_stmts(body_stmts)
                # while node takes the result of the *first* condition evaluation.
                return While(new_condition, new_body_stmts)
                # this assumes While can take a Begin node, which might not be true downstream.
            case _:
                return stmt


    def rco_stmts(stmts: List[Stmt]) -> List[Stmt]:
        all_stmts = []
        for stmt in stmts:
            new_stmts = []
            processed_stmt = rco_stmt(stmt, new_stmts)
            # add generated statements first, then the processed one
            all_stmts.extend(new_stmts)
            all_stmts.append(processed_stmt)
        return all_stmts


    def rco_exp(e: Expr, new_stmts: List[Stmt]) -> Expr:
         # ensure result is atomic (Var/Const) by assigning to temp var
        match e:
            case Constant(_) | Var(_):
                return e

            case Call(func, args):
                new_func = rco_exp(func, new_stmts) # atomize function expression
                new_args = [rco_exp(arg, new_stmts) for arg in args] # atomize args
                new_call = Call(new_func, new_args)
                # assign result to temporary variable
                temp_var = gensym('tmp_call')
                new_stmts.append(Assign(temp_var, new_call))
                return Var(temp_var)

            case Prim(op, args):
                new_args = [rco_exp(arg, new_stmts) for arg in args] # atomize args
                new_prim = Prim(op, new_args)
                temp_var = gensym(f'tmp_{op}')
                new_stmts.append(Assign(temp_var, new_prim))
                return Var(temp_var)

            case Begin(stmts, result_exp):
                 # process statements, generating their own temporaries via rco_stmts
                processed_stmts = rco_stmts(stmts)
                new_stmts.extend(processed_stmts) # add generated statements
                 # process the final expression, result should be atomic
                atomic_result = rco_exp(result_exp, new_stmts)
                return atomic_result

            case _:
                return e


    match prog:
        case Program(stmts):
            processed_stmts = rco_stmts(stmts)
            return Program(processed_stmts)
        case _:
             return prog

##################################################
# explicate-control
##################################################
# op     ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#          | "subscript" | "allocate" | "collect" | "tuple_set" # Note: tuple_set not in Lfun spec
# Expr   ::= Var(x) | Constant(n) | Prim(op, List[Expr])
#          | Call(Expr, List[Expr])
# Stmt   ::= Assign(x, Expr) | Print(Expr) | If(Expr, Stmts, Stmts) | While(Begin(Stmts, Expr), Stmts) # RCO output state
#          | Return(Expr) | FunctionDef(str, List[Tuple[str, type]], List[Stmt], type)
# Stmts  ::= List[Stmt]
# LFun   ::= Program(Stmts)

def explicate_control(prog: Program) -> cif.CProgram:
    """
    Transforms an Lfun Expression into a Cif program.
    :param prog: An Lfun Expression (post-RCO)
    :return: A Cif Program
    """

    all_func_defs = [] # cif.CFunctionDef objects

    # function to handle a single function's body
    def _explicate_body(current_function_name: str, body_prog: Program) -> Dict[str, List[cif.Stmt]]:
        """
        Transforms an Lfun Program (representing function body) into Cif basic blocks.
        :param current_function_name: Name for generating labels.
        :param body_prog: An Lfun Program instance containing the statements.
        :return: A dictionary of basic blocks {label: [cif.Stmt]}.
        """
        basic_blocks: Dict[str, List[cif.Stmt]] = {}
        start_label = current_function_name + '_start' # start label

        # --- Basic Block Helpers ---
        def create_block(stmts: List[cif.Stmt] = None) -> str:
            nonlocal basic_blocks # modification of outer scope dict
            label = gensym(current_function_name + '_label') # prefix labels
            basic_blocks[label] = stmts if stmts is not None else []
            return label

        def add_stmt(label: str, stmt: cif.Stmt):
            if label not in basic_blocks:
                 # create block if it doesn't exist
                 basic_blocks[label] = []
            basic_blocks[label].append(stmt)

        # --- Expression Explication ---
        def explicate_exp(e: Expr) -> cif.Expr:
            # translate Lfun expressions (atomic after RCO) to Cif expressions
            match e:
                case Var(x):
                    return cif.Var(x)
                case Constant(c):
                    if isinstance(c, bool):
                        return cif.Constant(c)
                    else:
                        return cif.Constant(c)
                case Prim(op, args):
                    new_args = [explicate_exp(a) for a in args]
                    return cif.Prim(op, new_args)
                case Call(func, args):
                    new_func = explicate_exp(func)
                    new_args = [explicate_exp(a) for a in args]
                    return cif.Call(new_func, new_args)
                case Begin(_, _):
                    # begin should ideally be handled by RCO or not present in atomic expressions
                    return cif.Constant(0)
                case _:
                    return cif.Constant(0)


        # --- Statement List Explication ---
        def explicate_stmts(stmts: List[Stmt], start_label: str) -> str:
            """ Processes a list of Lfun statements, returning the label of the last active block """
            current_label = start_label
            for s in stmts:
                current_label = explicate_stmt(s, current_label) # update current label
            return current_label

        # --- Statement Explication ---
        def explicate_stmt(stmt: Stmt, current_label: str) -> str:
            """ Processes a single Lfun statement, returning the next active block label """
            match stmt:
                case Assign(x, exp):
                    # already atomic due to RCO
                    new_exp = explicate_exp(exp)
                    add_stmt(current_label, cif.Assign(x, new_exp))
                    return current_label # continue in the same block
                case Print(exp):
                     # expression is atomic
                    new_exp = explicate_exp(exp)
                    add_stmt(current_label, cif.Print(new_exp))
                    return current_label
                case Return(e):
                    new_exp = explicate_exp(e)
                    add_stmt(current_label, cif.Return(new_exp))
                    return current_label

                case If(condition, then_stmts, else_stmts):
                    cond_exp = explicate_exp(condition)

                    then_label = create_block()
                    else_label = create_block()
                    cont_label = create_block()

                    # generate the conditional jump (comparing to 1 for True)
                    add_stmt(current_label, cif.If(cond_exp, cif.Goto(then_label), cif.Goto(else_label)))

                    # process the 'then' branch
                    then_cont_label = explicate_stmts(then_stmts, then_label)
                    add_stmt(then_cont_label, cif.Goto(cont_label)) # jump from end of 'then' to continuation

                    # process the 'else' branch
                    else_cont_label = explicate_stmts(else_stmts, else_label)
                    add_stmt(else_cont_label, cif.Goto(cont_label)) # jump from end of 'else' to continuation

                    return cont_label

                case While(condition, body_stmts):
                     check_label = create_block()
                     body_label = create_block()
                     cont_label = create_block()

                     add_stmt(current_label, cif.Goto(check_label)) # jump into the loop check first

                     # process the loop body
                     body_cont_label = explicate_stmts(body_stmts, body_label)
                     # after body, jump back to check condition again
                     add_stmt(body_cont_label, cif.Goto(check_label))

                     # Process the check block
                     cond_exp = explicate_exp(condition)
                     add_stmt(check_label, cif.If(cond_exp, cif.Goto(body_label), cif.Goto(cont_label)))

                     return cont_label

                     return current_label


        # --- Main logic for _explicate_body ---
        match body_prog:
             case Program(stmts):
                  basic_blocks[start_label] = []
                  conclusion_label = explicate_stmts(stmts, start_label)
                  if current_function_name == 'main':
                      if not basic_blocks[conclusion_label] or not isinstance(basic_blocks[conclusion_label][-1], cif.Return):
                           add_stmt(conclusion_label, cif.Return(cif.Constant(0)))
                  return basic_blocks
             case _:
                  return {}


    # --- Main logic for explicate_control ---
    match prog:
        case Program(stmts):
            regular_stmts = []
            # separate FunctionDefs from main code
            for s in stmts:
                if isinstance(s, FunctionDef):
                    param_names = [p[0] for p in s.params]
                    # explicate function body
                    func_blocks = _explicate_body(s.name, Program(s.body_stmts))
                    all_func_defs.append(cif.CFunctionDef(s.name, param_names, func_blocks))
                else:
                    regular_stmts.append(s)

            # explicate main code
            main_blocks = _explicate_body('main', Program(regular_stmts))
            all_func_defs.append(cif.CFunctionDef('main', [], main_blocks))

            return cif.CProgram(all_func_defs)
        case _:
            return cif.CProgram([])


##################################################
# select-instructions
##################################################
# op           ::= "add" | "sub" | "mult" | "not" | "or" | "and" | "eq" | "gt" | "gte" | "lt" | "lte"
#                | "subscript" | "allocate" | "collect" | "tuple_set"
# Expr         ::= Var(x) | Constant(n) | Prim(op, List[Expr])
# Stmt         ::= Assign(x, Expr) | Print(Expr)
#                | If(Expr, Goto(label), Goto(label)) | Goto(label) | Return(Expr)
# Stmts        ::= List[Stmt]
# CFunctionDef ::= CFunctionDef(name, List[str], Dict[label, Stmts])
# Cif         ::= CProgram(List[CFunctionDef])

@dataclass(frozen=True, eq=True)
class X86FunctionDef(AST):
    label: str
    blocks: Dict[str, List[x86.Instr]]
    stack_space: Tuple[int, int]

@dataclass(frozen=True, eq=True)
class X86ProgramDefs(AST):
    defs: List[X86FunctionDef]

def select_instructions(prog: cif.CProgram) -> X86ProgramDefs:
    """
    Transforms a Lfun program into a pseudo-x86 assembly program.
    :param prog: a Lfun program
    :return: a pseudo-x86 program
    """

    function_defs = []

    match prog:
        case cif.CProgram(defs):
            for d in defs:
                match d:
                    case cif.CFunctionDef(name, args, blocks):
                        p = _select_instructions(name, cif.CProgram(blocks))
                        match p:
                            case x86.X86Program(new_blocks):
                                setup_instrs = [x86.Movq(x86.Reg(r), x86.Var(a)) \
                                                for a, r in zip(args, constants.argument_registers)]
                                new_blocks[name + 'start'] = setup_instrs + new_blocks[name + 'start']

                                function_defs.append(X86FunctionDef(name, new_blocks, None))
            return X86ProgramDefs(function_defs)

PRINT_VALUE_LABEL = "print_value"
ALLOCATE_LABEL = "allocate"       # label for allocation function
COLLECT_LABEL = "collect"

def _select_instructions(current_function: str, prog: cif.CProgram) -> x86.X86Program:
    """
    Transforms a Cif program into a pseudo-x86 assembly program.
    :param prog: a Cif program
    :return: a pseudo-x86 program
    """

    function_names = set()

    # convert Cif expressions (atoms) to x86 arguments, tagging constants.
    def si_expr(a: cif.Expr) -> x86.Arg:
        match a:
            case cif.Constant(i) if isinstance(i, bool):
                 tagged_val = 2 if i else 0
                 return x86.Immediate(tagged_val)
            case cif.Constant(i) if isinstance(i, int):
                 tagged_val = i << 1
                 return x86.Immediate(tagged_val)
            case cif.Var(x):
                return x86.Var(x)
            case cif.Prim(op, args):
                 raise Exception(f"EXPERIMENTAL: Primitives should be handled in Assign statement: {a}")
            case _:
                raise Exception(f'si_expr unhandled expression type: {type(a)}, {a}')

    # process a list of Cif statements
    def si_stmts(stmts: List[cif.Stmt]) -> List[x86.Instr]:
        instrs = []
        for stmt in stmts:
            instrs.extend(si_stmt(stmt))
        return instrs

    # map comparison operations to x86
    op_cc = {'eq': 'e', 'gt': 'g', 'gte': 'ge', 'lt': 'l', 'lte': 'le'}

    # generate instructions for a single Cif statement.
    def si_stmt(stmt: cif.Stmt) -> List[x86.Instr]:
        match stmt:
            case cif.Assign(x, expr):
                dest_var = x86.Var(x)

                match expr:
                    # handle simple variable or constant assignments
                    case cif.Constant(_) | cif.Var(_):
                        return [x86.Movq(si_expr(expr), dest_var)]

                    # instructions for addition
                    case cif.Prim('add', [arg1, arg2]):
                        instrs = [
                            x86.Movq(si_expr(arg1), x86.Reg('rax')),
                            x86.Movq(si_expr(arg2), x86.Reg('r11')),
                            x86.Movq(x86.Reg('rax'), x86.Reg('rbx')),
                            x86.Orq(x86.Reg('r11'), x86.Reg('rbx')),
                            x86.Testq(x86.Immediate(1), x86.Reg('rbx')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('r11')),
                            x86.Addq(x86.Reg('r11'), x86.Reg('rax')),
                            x86.Salq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Movq(x86.Reg('rax'), dest_var)
                        ]
                        return instrs

                    # instructions for subtraction
                    case cif.Prim('sub', [arg1, arg2]):
                        instrs = [
                            x86.Movq(si_expr(arg1), x86.Reg('rax')),
                            x86.Movq(si_expr(arg2), x86.Reg('r11')),
                            x86.Movq(x86.Reg('rax'), x86.Reg('rbx')),
                            x86.Orq(x86.Reg('r11'), x86.Reg('rbx')),
                            x86.Testq(x86.Immediate(1), x86.Reg('rbx')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('r11')),
                            x86.Subq(x86.Reg('r11'), x86.Reg('rax')),
                            x86.Salq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Movq(x86.Reg('rax'), dest_var)
                        ]
                        return instrs

                    # instructions for comparison operations
                    case cif.Prim(op, [arg1, arg2]) if op in op_cc:
                        instrs = [
                            x86.Movq(si_expr(arg1), x86.Reg('rax')),
                            x86.Movq(si_expr(arg2), x86.Reg('r11')),
                            x86.Movq(x86.Reg('rax'), x86.Reg('rbx')),
                            x86.Orq(x86.Reg('r11'), x86.Reg('rbx')),
                            x86.Testq(x86.Immediate(1), x86.Reg('rbx')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('r11')),
                            x86.Cmpq(x86.Reg('r11'), x86.Reg('rax')),
                            x86.Set(op_cc[op], x86.ByteReg('bl')),
                            x86.Movzbq(x86.ByteReg('bl'), x86.Reg('rax')),
                            x86.Salq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Movq(x86.Reg('rax'), dest_var)
                        ]
                        return instrs

                    # instructions for logical not
                    case cif.Prim('not', [arg1]):
                        is_false_label = gensym(f"{current_function}_not_is_false")
                        done_label = gensym(f"{current_function}_not_done")
                        instrs = [
                            x86.Movq(si_expr(arg1), x86.Reg('rax')),
                            x86.Cmpq(x86.Immediate(0), x86.Reg('rax')),
                            x86.Je(is_false_label),
                            x86.Movq(x86.Immediate(0), x86.Reg('rax')),
                            x86.Jmp(done_label),
                           f"{is_false_label}:",
                            x86.Movq(x86.Immediate(2), x86.Reg('rax')),
                           f"{done_label}:",
                            x86.Movq(x86.Reg('rax'), dest_var)
                        ]
                        return instrs

                    # instructions to create a tuple
                    case cif.Prim('tuple', args):
                        num_args = len(args)
                        alloc_size = 8 * (1 + num_args)
                        instrs = [
                            x86.Movq(x86.Immediate(alloc_size), x86.Reg('rdi')),
                            x86.Callq(ALLOCATE_LABEL),
                            x86.Movq(x86.Reg('rax'), x86.Reg('r11')),
                            x86.Movq(x86.Immediate(num_args), x86.Deref('r11', 0)),
                        ]
                        temp_reg_tuple = x86.Reg('rbx')
                        for i, arg in enumerate(args):
                            offset = 8 * (i + 1)
                            arg_val = si_expr(arg)
                            needs_move = False
                            if not isinstance(arg_val, x86.Immediate):
                                if isinstance(arg_val, x86.Reg) and arg_val.reg == 'r11':
                                    needs_move = True
                                elif not isinstance(arg_val, x86.Reg):
                                    needs_move = True
                            if needs_move:
                                instrs.append(x86.Movq(arg_val, temp_reg_tuple))
                                value_to_store = temp_reg_tuple
                            else:
                                value_to_store = arg_val
                            instrs.append(x86.Movq(value_to_store, x86.Deref('r11', offset)))
                        instrs.extend([
                            x86.Orq(x86.Immediate(1), x86.Reg('r11')),
                            x86.Movq(x86.Reg('r11'), dest_var)
                        ])
                        return instrs

                    # instructions for tuple element access.
                    case cif.Prim('subscript', [tuple_expr, index_expr]):
                        instrs = [
                            x86.Movq(si_expr(tuple_expr), x86.Reg('r11')),
                            x86.Movq(si_expr(index_expr), x86.Reg('rax')),
                            x86.Testq(x86.Immediate(1), x86.Reg('r11')),
                            x86.Testq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Sarq(x86.Immediate(1), x86.Reg('rax')),
                            x86.Andq(x86.Immediate(~1), x86.Reg('r11')),
                            x86.Movq(x86.Deref('r11', 0), x86.Reg('rbx')),
                            x86.Cmpq(x86.Reg('rax'), x86.Immediate(0)),
                            x86.Cmpq(x86.Reg('rax'), x86.Reg('rbx')),
                            x86.Leaq(x86.Deref('r11', 8), x86.Reg('r11')),
                            x86.Movq(x86.Deref('r11', 0, 'rax', 8), x86.Reg('rbx')),
                            x86.Movq(x86.Reg('rbx'), dest_var)
                        ]
                        return instrs

                    # instructions for function calls.
                    case cif.Call(fun, args):
                        instrs = []
                        saved_regs = [r for r in constants.caller_saved_registers if r != 'rax']
                        for r in saved_regs:
                            instrs.append(x86.Pushq(x86.Reg(r)))
                        temp_reg_call = x86.Reg('rbx')
                        for arg_expr, reg_name in zip(args, constants.argument_registers):
                            arg_val = si_expr(arg_expr)
                            target_reg = x86.Reg(reg_name)
                            if arg_val == target_reg:
                                continue
                            arg_val_to_move = arg_val
                            if not isinstance(arg_val, (x86.Immediate, x86.Reg)):
                                instrs.append(x86.Movq(arg_val, temp_reg_call))
                                arg_val_to_move = temp_reg_call
                            instrs.append(x86.Movq(arg_val_to_move, target_reg))
                        match fun:
                            case cif.Var(f) if f in function_names:
                                instrs.append(x86.Callq(f))
                            case _:
                                fun_ptr = si_expr(fun)
                                temp_reg_fun = x86.Reg('rax')
                                if fun_ptr != temp_reg_fun:
                                     instrs.append(x86.Movq(fun_ptr, temp_reg_fun))
                                instrs.append(x86.IndirectCallq(temp_reg_fun))
                        for r in reversed(saved_regs):
                            instrs.append(x86.Popq(x86.Reg(r)))
                        instrs.append(x86.Movq(x86.Reg('rax'), dest_var))
                        return instrs

                    # Hunknown primitive operations
                    case _:
                         raise Exception(f"si_stmt Assign: unhandled expression type {type(expr)}: {expr}")

            # instructions for printing a value
            case cif.Print(atm1):
                return [
                    x86.Movq(si_expr(atm1), x86.Reg('rdi')),
                    x86.Callq(PRINT_VALUE_LABEL)
                ]

            # instructions to return a value from a function
            case cif.Return(atm1):
                return [
                    x86.Movq(si_expr(atm1), x86.Reg('rax')),
                    x86.Jmp(current_function + 'conclusion')
                ]

            # unconditional jump
            case cif.Goto(label):
                return [x86.Jmp(label)]

            # instructions for conditional branching
            case cif.If(cond_expr, cif.Goto(then_label), cif.Goto(else_label)):
                cond_val = si_expr(cond_expr)
                instrs = []
                if not isinstance(cond_val, x86.Reg) or cond_val.reg != 'rax':
                     instrs.append(x86.Movq(cond_val, x86.Reg('rax')))
                instrs.extend([
                    x86.Cmpq(x86.Immediate(0), x86.Reg('rax')),
                    x86.Je(else_label),
                    x86.Jmp(then_label)
                ])
                return instrs

            # unknown statement types
            case _:
                raise Exception(f'si_stmt unhandled statement type: {type(stmt)}, {stmt}')

    match prog:
        case cif.CProgram(basic_blocks):
            generated_blocks = {}
            for label, block in basic_blocks.items():
                 generated_blocks[str(label)] = si_stmts(block)
            return x86.X86Program(generated_blocks)
        case _:
            raise Exception('select_instructions', prog)


##################################################
# allocate-registers
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq' | 'leaq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= op(Arg, Arg) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | IndirectCallq(Arg)
# Blocks ::= Dict[label, List[Instr]]

# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

Color = int
Coloring = Dict[x86.Var, Color]
Saturation = Set[Color]

def allocate_registers(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    match program:
        case X86ProgramDefs(defs):
            new_defs = []
            for d in defs:
                new_program = _allocate_registers(d.label, x86.X86Program(d.blocks))
                new_defs.append(X86FunctionDef(d.label, new_program.blocks, new_program.stack_space))
            return X86ProgramDefs(new_defs)


def _allocate_registers(current_function: str, program: x86.X86Program) -> x86.X86Program:
    """
    Assigns homes to variables in the input program. Allocates registers and
    stack locations as needed, based on a graph-coloring register allocation
    algorithm.
    :param program: A pseudo-x86 program.
    :return: An x86 program, annotated with the number of bytes needed in stack
    locations.
    """

    blocks = program.blocks
    live_before_sets = {current_function + 'conclusion': set()}
    for label in blocks:
        live_before_sets[label] = set()
    live_after_sets = {}
    homes: Dict[x86.Var, x86.Arg] = {}
    tuple_homes: Dict[x86.Var, x86.Arg] = {}
    tuple_vars = set(tuple_var_types.keys())

    # --------------------------------------------------
    # utilities
    # --------------------------------------------------
    # Determine variables used within an x86 argument.
    def vars_arg(a: x86.Arg) -> Set[x86.Var]:
        match a:
            case x86.Immediate(i):
                return set()
            case x86.GlobalVal(v):
                return set()
            case x86.Reg(r):
                return set()
            case x86.ByteReg(r):
                return set()
            case x86.Var(x):
                if x in tuple_var_types:
                    return set()
                else:
                    return {x86.Var(x)}
            case x86.Deref(r, offset):
                return set()
            case _:
                raise Exception('vars_arg', a)

    def reads_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.Movq(e1, _) | x86.Movzbq(e1, _) | x86.Pushq(e1) | x86.IndirectCallq(e1):
                return vars_arg(e1)
            case x86.Addq(e1, e2) | x86.Cmpq(e1, e2) | x86.Imulq(e1, e2) | \
                 x86.Subq(e1, e2) | x86.Andq(e1, e2) | x86.Orq(e1, e2) | x86.Xorq(e1, e2) | \
                 x86.Leaq(e1, e2):
                return vars_arg(e1).union(vars_arg(e2))
            case x86.Jmp(label) | x86.JmpIf(_, label):
                return live_before_sets[label]
            case x86.Callq(_) | x86.Set(_, _) | x86.Popq(_):
                 return set()
            case _:
                 if isinstance(i, (x86.Retq)):
                     return set()
                 else:
                     raise Exception(i)

    def writes_of(i: x86.Instr) -> Set[x86.Var]:
        match i:
            case x86.Movq(_, e2) | x86.Movzbq(_, e2) | \
                 x86.Addq(_, e2) | x86.Subq(_, e2) | x86.Imulq(_, e2) | \
                 x86.Andq(_, e2) | x86.Orq(_, e2) | x86.Xorq(_, e2) | \
                 x86.Popq(e2) | x86.Leaq(_, e2):
                return vars_arg(e2)
            case x86.Cmpq(_, _):
                 return set()
            case x86.Jmp(_) | x86.JmpIf(_, _) | x86.Callq(_) | x86.Set(_, _) | \
                 x86.IndirectCallq(_) | x86.Pushq(_) | x86.Retq():
                return set()
            case _:
                raise Exception(i)


    # --------------------------------------------------
    # liveness analysis
    # --------------------------------------------------
    # Calculate live variables before an instruction.
    def ul_instr(i: x86.Instr, live_after: Set[x86.Var]) -> Set[x86.Var]:
        return live_after.difference(writes_of(i)).union(reads_of(i))

    def ul_block(label: str):
        instrs = blocks[label]
        # determine live_after for the last instruction based on successors.
        last_instr = instrs[-1] if instrs else None
        current_live_after: Set[x86.Var] = set()
        if isinstance(last_instr, (x86.Jmp)):
             current_live_after = live_before_sets.get(last_instr.label, set())
        elif isinstance(last_instr, (x86.JmpIf)):
             # combine live sets from both potential targets
             then_live = live_before_sets.get(last_instr.label, set())
             current_live_after = live_before_sets.get(last_instr.label, set())
        elif isinstance(last_instr, (x86.Retq)):
            current_live_after = set()
        else:
             pass


        block_live_after_sets = []
        for i in reversed(instrs):
            block_live_after_sets.append(current_live_after)
            current_live_after = ul_instr(i, current_live_after)

        live_before_sets[label] = current_live_after
        live_after_sets[label] = list(reversed(block_live_after_sets))

    def ul_fixpoint():
        # initialize live_after for the last block (conclusion) - empty
        live_after_sets[current_function + 'conclusion'] = []

        # successor map (for accurate live_after)
        successors = {label: [] for label in blocks}
        for label, instrs in blocks.items():
             if instrs:
                 last_instr = instrs[-1]
                 if isinstance(last_instr, x86.Jmp):
                     successors[label].append(last_instr.label)
                 elif isinstance(last_instr, x86.JmpIf):
                     successors[label].append(last_instr.label)
                     block_keys = list(blocks.keys())
                     current_index = block_keys.index(label)
                     if current_index + 1 < len(block_keys):
                          fallthrough_label = block_keys[current_index+1]
                          # avoid adding jump target twice if it's the immediate next block
                          if fallthrough_label != last_instr.label:
                               successors[label].append(fallthrough_label)

                 elif not isinstance(last_instr, x86.Retq):
                      block_keys = list(blocks.keys())
                      current_index = block_keys.index(label)
                      if current_index + 1 < len(block_keys):
                           successors[label].append(block_keys[current_index+1])
             elif label != current_function + 'conclusion':
                  block_keys = list(blocks.keys())
                  current_index = block_keys.index(label)
                  if current_index + 1 < len(block_keys):
                      successors[label].append(block_keys[current_index+1])


        labels = list(blocks.keys())
        changed = True
        while changed:
            changed = False
            for label in reversed(labels):
                # calculate live_after for the block based on successors' live_before
                current_block_live_after = set()
                for succ_label in successors.get(label, []):
                    current_block_live_after.update(live_before_sets.get(succ_label, set()))

                initial_live_after = current_block_live_after

                # process the block instructions backwards
                block_instrs = blocks.get(label, [])
                block_live_after_list = []
                temp_live_after = initial_live_after
                for instr in reversed(block_instrs):
                    block_live_after_list.append(temp_live_after)
                    temp_live_after = ul_instr(instr, temp_live_after)

                # check if live_before set changed for this block
                old_live_before = live_before_sets.get(label, set())
                if temp_live_after != old_live_before:
                    live_before_sets[label] = temp_live_after
                    changed = True

                live_after_sets[label] = list(reversed(block_live_after_list))


    # --------------------------------------------------
    # interference graph
    # --------------------------------------------------
    def bi_instr(e: x86.Instr, live_after: Set[x86.Var], graph: InterferenceGraph):
        for v1 in writes_of(e):
            for v2 in live_after:
                if v1 != v2:
                     if isinstance(e, x86.Movq) and v1 == writes_of(e).pop() and v2 == reads_of(e).pop():
                          pass
                     else:
                          graph.add_edge(v1, v2)

    def bi_block(instrs: List[x86.Instr], live_afters: List[Set[x86.Var]], graph: InterferenceGraph):
        if len(instrs) != len(live_afters):
             if len(live_afters) == 0 and len(instrs) > 0 : # if live_afters is empty, use empty set
                  live_afters = [set()] * len(instrs)
             elif len(live_afters) > 0: # pad with last known live set
                  live_afters = live_afters + [live_afters[-1]] * (len(instrs) - len(live_afters))
             else:
                  pass

        for instr, live_after in zip(instrs, live_afters):
            bi_instr(instr, live_after, graph)

    # --------------------------------------------------
    # graph coloring
    # --------------------------------------------------
    def color_graph(local_vars: Set[x86.Var], interference_graph: InterferenceGraph) -> Coloring:
        coloring: Coloring = {}
        to_color = local_vars.copy()
        saturation_sets = {x: set() for x in local_vars}

        while to_color:
            # Find variable with the largest saturation set.
            x = max(to_color, key=lambda var: len(saturation_sets.get(var, set())))
            to_color.remove(x)

            # Find the smallest available color (integer).
            x_neighbors = interference_graph.neighbors(x)
            neighbor_colors = {coloring[n] for n in x_neighbors if n in coloring}
            x_color = 0
            while x_color in neighbor_colors:
                 x_color += 1

            # Assign x's color.
            coloring[x] = x_color

        colored_vars = set()
        sorted_vars = sorted(list(local_vars), key=lambda v: interference_graph.degree(v), reverse=True) # Degree heuristic

        for var in sorted_vars:
             neighbor_colors = set()
             for neighbor in interference_graph.neighbors(var):
                  if neighbor in coloring:
                       neighbor_colors.add(coloring[neighbor])

             c = 0
             while c in neighbor_colors:
                  c += 1
             coloring[var] = c


        return coloring


    # --------------------------------------------------
    # assigning homes
    # --------------------------------------------------
    def align(num_bytes: int) -> int:
        return (num_bytes + 15) & ~15

    def ah_arg(a: x86.Arg) -> x86.Arg:
        match a:
            case x86.Immediate(_) | x86.GlobalVal(_) | x86.Reg(_) | x86.ByteReg(_) | x86.Deref(_, _):
                return a
            case x86.Var(x):
                var_node = x86.Var(x)
                if x in tuple_vars:
                    if var_node not in tuple_homes:
                        offset = -(len(tuple_homes) * 8 + 8)
                        tuple_homes[var_node] = x86.Deref('r15', offset)
                    return tuple_homes[var_node]
                else:
                    if var_node in homes:
                        return homes[var_node]
                    else:
                        return x86.Deref('rbp', -999) # placeholder

            case _:
                raise Exception('ah_arg', a)

    def ah_instr(e: x86.Instr) -> x86.Instr:
        match e:
            case x86.Movq(a1, a2):
                return x86.Movq(ah_arg(a1), ah_arg(a2))
            case x86.Movzbq(a1, a2):
                return x86.Movzbq(ah_arg(a1), ah_arg(a2))
            case x86.Addq(a1, a2):
                return x86.Addq(ah_arg(a1), ah_arg(a2))
            case x86.Subq(a1, a2):
                return x86.Subq(ah_arg(a1), ah_arg(a2))
            case x86.Imulq(a1, a2):
                return x86.Imulq(ah_arg(a1), ah_arg(a2))
            case x86.Cmpq(a1, a2):
                return x86.Cmpq(ah_arg(a1), ah_arg(a2))
            case x86.Andq(a1, a2):
                return x86.Andq(ah_arg(a1), ah_arg(a2))
            case x86.Orq(a1, a2):
                return x86.Orq(ah_arg(a1), ah_arg(a2))
            case x86.Xorq(a1, a2):
                return x86.Xorq(ah_arg(a1), ah_arg(a2))
            case x86.Set(cc, a1):
                return x86.Set(cc, ah_arg(a1))
            case x86.Pushq(a1):
                return x86.Pushq(ah_arg(a1))
            case x86.Popq(a1):
                return x86.Popq(ah_arg(a1))
            case x86.IndirectCallq(a1):
                 return x86.IndirectCallq(ah_arg(a1))
            case x86.Leaq(a1, a2): return x86.Leaq(ah_arg(a1), ah_arg(a2))
            case x86.Callq(_, _) | x86.Retq() | x86.Jmp(_) | x86.JmpIf(_, _):
                return e
            case _:
                raise Exception('ah_instr', e)

    def ah_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        return [ah_instr(i) for i in instrs]

    # --------------------------------------------------
    # main body of the pass
    # --------------------------------------------------

    # Step 1: Perform liveness analysis.
    ul_fixpoint()
    log_ast('live-after sets', live_after_sets)

    # Step 2: Build the interference graph.
    interference_graph = InterferenceGraph()
    for label in blocks.keys():
        # ensure live_after_sets[label] exists and aligns with block length before passing
        block_live_afters = live_after_sets.get(label, [])
        num_instrs = len(blocks.get(label,[]))
        if len(block_live_afters) < num_instrs:
             if not block_live_afters: block_live_afters = [set()] * num_instrs
             else: block_live_afters += [block_live_afters[-1]] * (num_instrs-len(block_live_afters))

        bi_block(blocks[label], block_live_afters, interference_graph)

    log_ast('interference graph', interference_graph)

    # Step 3: Color the graph.
    all_vars = interference_graph.get_nodes()
    # only Var instances are colored
    vars_to_color = {v for v in all_vars if isinstance(v, x86.Var)}
    # exclude tuple vars if they are handled separately by r15 (though they might be empty)
    vars_to_color = vars_to_color - {x86.Var(tv) for tv in tuple_vars}

    coloring = color_graph(vars_to_color, interference_graph)
    colors_used = set(coloring.values())
    log('coloring', coloring)

    available_registers = list(constants.caller_saved_registers + constants.callee_saved_registers)

    # Step 4: map colors to actual homes (registers or stack slots)
    color_map = {}
    stack_locations_used = 0

    # assign registers first, then spill to stack
    for color in sorted(list(colors_used)): # deterministic order
        if available_registers:
            # pop from end might be better for typical usage (higher regs first?)
            r = available_registers.pop(0) # use lower registers first
            color_map[color] = x86.Reg(r)
        else:
            stack_locations_used += 1
            offset = -(stack_locations_used * 8)
            color_map[color] = x86.Deref('rbp', offset)

    # Step 4.2: create the final 'homes' dictionary mapping Var -> Home
    for var_node in vars_to_color: # use the set that was actually colored
        if var_node in coloring: # check if var got a color
             homes[var_node] = color_map[coloring[var_node]]

    log('homes', homes)

    # Step 5: replace variables with their assigned homes in the code blocks
    new_blocks = {label: ah_block(block) for label, block in blocks.items()}

    regular_stack_space = align(8 * stack_locations_used)
    root_stack_slots = len(tuple_homes)

    return x86.X86Program(new_blocks, stack_space = (regular_stack_space, root_stack_slots))




##################################################
# patch-instructions
##################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq' | 'leaq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= op(Arg, Arg) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | IndirectCallq(Arg)
# Blocks ::= Dict[label, List[Instr]]

# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

def patch_instructions(program: X86ProgramDefs) -> X86ProgramDefs:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    match program:
        case X86ProgramDefs(defs):
            new_defs = []
            for d in defs:
                # Patch instructions within the function's blocks.
                new_prog = _patch_instructions(x86.X86Program(d.blocks, d.stack_space))
                new_defs.append(X86FunctionDef(d.label, new_prog.blocks, new_prog.stack_space))
            return X86ProgramDefs(new_defs)


def _patch_instructions(program: x86.X86Program) -> x86.X86Program:
    """
    Patches instructions with two memory location inputs, using %rax as a temporary location.
    :param program: An x86 program.
    :return: A patched x86 program.
    """

    def pi_instr(e: x86.Instr) -> List[x86.Instr]:
        match e:
            case x86.Cmpq(x86.Deref(_, _), x86.Immediate(i)):
                 return [x86.Movq(x86.Immediate(i), x86.Reg('rax')),
                         x86.Cmpq(e.arg1, x86.Reg('rax'))]
            case x86.Cmpq(x86.Immediate(i), x86.Deref(_, _)):
                 return [x86.Movq(x86.Immediate(i), x86.Reg('rax')),
                         x86.Cmpq(x86.Reg('rax'), e.arg2)]
            case x86.Movq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                return [x86.Movq(x86.Deref(r1, o1), x86.Reg('rax')),
                        x86.Movq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Movzbq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                return [x86.Movzbq(x86.Deref(r1, o1), x86.Reg('rax')),
                        x86.Movq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Addq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                return [x86.Movq(x86.Deref(r1, o1), x86.Reg('rax')),
                        x86.Addq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Subq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                 return [x86.Movq(x86.Deref(r1,o1), x86.Reg('rax')),
                         x86.Subq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Imulq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                 return [x86.Movq(x86.Deref(r1,o1), x86.Reg('rax')),
                         x86.Imulq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Andq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                 return [x86.Movq(x86.Deref(r1,o1), x86.Reg('rax')),
                         x86.Andq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Orq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                 return [x86.Movq(x86.Deref(r1,o1), x86.Reg('rax')),
                         x86.Orq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case x86.Xorq(x86.Deref(r1, o1), x86.Deref(r2, o2)):
                 return [x86.Movq(x86.Deref(r1,o1), x86.Reg('rax')),
                         x86.Xorq(x86.Reg('rax'), x86.Deref(r2, o2))]
            case _:
                return [e]

    def pi_block(instrs: List[x86.Instr]) -> List[x86.Instr]:
        new_instrs = []
        for i in instrs:
            new_instrs.extend(pi_instr(i))
        return new_instrs

    match program:
        case x86.X86Program(blocks, stack_space):
            new_blocks = {label: pi_block(block) for label, block in blocks.items()}
            return x86.X86Program(new_blocks, stack_space = stack_space)


##################################################
# prelude-and-conclusion
###################################################
# Arg    ::= Immediate(i) | Reg(r) | ByteReg(r) | Var(x) | Deref(r, offset) | GlobalVal(x)
# op     ::= 'addq' | 'cmpq' | 'andq' | 'orq' | 'xorq' | 'movq' | 'movzbq' | 'leaq'
# cc     ::= 'e'| 'g' | 'ge' | 'l' | 'le'
# Instr  ::= op(Arg, Arg) | Callq(label) | Retq()
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | Jmp(label) | JmpIf(cc, label) | Set(cc, Arg)
#         | IndirectCallq(Arg)
# Blocks ::= Dict[label, List[Instr]]

# X86FunctionDef ::= X86FunctionDef(name, Blocks)
# X86ProgramDefs ::= List[X86FunctionDef]

def prelude_and_conclusion(program: X86ProgramDefs) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """

    match program:
        case X86ProgramDefs(defs):
            all_blocks = {}
            for d in defs:
                new_prog = _prelude_and_conclusion(d.label, x86.X86Program(d.blocks, d.stack_space))
                match new_prog:
                    case x86.X86Program(blocks, _):
                        for label, instrs in blocks.items():
                            all_blocks[label] = instrs
            return x86.X86Program(all_blocks)


def _prelude_and_conclusion(current_function: str, program: x86.X86Program) -> x86.X86Program:
    """
    Adds the prelude and conclusion for the program.
    :param program: An x86 program.
    :return: An x86 program, with prelude and conclusion.
    """
    stack_bytes, root_stack_locations = program.stack_space

    # Prelude
    prelude = [x86.Pushq(x86.Reg('rbp')),
               x86.Movq(x86.Reg('rsp'), x86.Reg('rbp'))]

    for r in constants.callee_saved_registers:
        prelude.append(x86.Pushq(x86.Reg(r)))

    prelude.append(x86.Subq(x86.Immediate(stack_bytes), x86.Reg('rsp')))

    if current_function == 'main':
        prelude.extend([
            # pass heap and root stack sizes to runtime initialization
            x86.Movq(x86.Immediate(constants.root_stack_size), x86.Reg('rdi')),
            x86.Movq(x86.Immediate(constants.heap_size), x86.Reg('rsi')),
            x86.Callq('initialize'),
            # set up root stack pointer %r15
            x86.Movq(x86.GlobalVal('rootstack_begin'), x86.Reg('r15'))
        ])

    if root_stack_locations > 0 :
         prelude.append(x86.Subq(x86.Immediate(8*root_stack_locations), x86.Reg('r15')))

    # jump to the actual start block of the function code
    prelude.append(x86.Jmp(current_function + 'start'))

    conclusion = []
    # deallocate root stack space if allocated
    if root_stack_locations > 0:
        conclusion.append(x86.Addq(x86.Immediate(8*root_stack_locations), x86.Reg('r15')))

    # deallocate local variable stack space
    conclusion.append(x86.Addq(x86.Immediate(stack_bytes), x86.Reg('rsp')))

    # restore callee-saved registers in reverse order
    for r in reversed(constants.callee_saved_registers):
        conclusion.append(x86.Popq(x86.Reg(r)))

    # restore base pointer and return
    conclusion.extend([
        x86.Popq(x86.Reg('rbp')),
        x86.Retq()
    ])

    new_blocks = program.blocks.copy()
    new_blocks[current_function] = prelude
    new_blocks[current_function + 'conclusion'] = conclusion

    return x86.X86Program(new_blocks, stack_space = program.stack_space)


##################################################
# add-allocate
##################################################

def add_allocate(program: str) -> str:
    """
    Adds the 'allocate' function to the end of the program.
    :param program: An x86 program, as a string.
    :return: An x86 program, as a string, with the 'allocate' function.
    """

    alloc = """
allocate:
  movq free_ptr(%rip), %rax
  addq %rdi, %rax
  movq %rdi, %rsi
  cmpq fromspace_end(%rip), %rax
  jl allocate_alloc
  movq %r15, %rdi
  callq collect
  jmp allocate_alloc
allocate_alloc:
  movq free_ptr(%rip), %rax
  addq %rsi, free_ptr(%rip)
  retq
"""
    return program + alloc

##################################################
# Compiler definition
##################################################

compiler_passes = {
    'typecheck': typecheck,
    'remove complex opera*': rco,
    'typecheck2': typecheck,
    'explicate control': explicate_control,
    'select instructions': select_instructions,
    'allocate registers': allocate_registers,
    'patch instructions': patch_instructions,
    'prelude & conclusion': prelude_and_conclusion,
    'print x86': x86.print_x86,
    'add allocate': add_allocate
}


def run_compiler(s, logging=False):
    global tuple_var_types, function_names
    tuple_var_types = {}
    function_names = set()

    def print_prog(current_program):
        print('Concrete syntax:')
        if isinstance(current_program, x86.X86Program):
            print(x86.print_x86(current_program))
        elif isinstance(current_program, X86ProgramDefs):
            print(print_x86defs.print_x86_defs(current_program))
        elif isinstance(current_program, Program):
            print(print_program(current_program))
        elif isinstance(current_program, cif.CProgram):
            print(cif.print_program(current_program))

        print()
        print('Abstract syntax:')
        print(print_ast(current_program))

    current_program = parse(s)

    if logging == True:
        print()
        print('==================================================')
        print(' Input program')
        print('==================================================')
        print()
        print_prog(current_program)

    for pass_name, pass_fn in compiler_passes.items():
        current_program = pass_fn(current_program)

        if logging == True:
            print()
            print('==================================================')
            print(f' Output of pass: {pass_name}')
            print('==================================================')
            print()
            print_prog(current_program)

    return current_program


if __name__ == '__main__':
    if len(sys.argv) != 2:
        print('Usage: python compiler.py <source filename>')
    else:
        file_name = sys.argv[1]
        with open(file_name) as f:
            print(f'Compiling program {file_name}...')

            try:
                program = f.read()
                x86_program = run_compiler(program, logging=True)

                with open(file_name + '.s', 'w') as output_file:
                    output_file.write(x86_program)

            except:
                print('Error during compilation! **************************************************')
                traceback.print_exception(*sys.exc_info())