import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import interp_Llambda
import type_check_Clambda
import type_check_Llambda
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

typecheck = type_check_Llambda.TypeCheckLlambda().type_check

typecheck_cTup = type_check_Clambda.TypeCheckClambda().type_check

typecheck_dict = {
    'source': typecheck,
    'shrink': typecheck,
    'uniquify': typecheck,
    'reveal_functions': typecheck,
    'convert_assignments': typecheck,
    'convert_to_closures': typecheck,
    'limit_functions': typecheck,
    'resolve': typecheck,
    'check_bounds': typecheck,
    'expose_allocation': typecheck,
    'remove_complex_operands': typecheck,
    'explicate_control': typecheck_cTup,
    'select_instructions': typecheck_cTup,
    'assign_homes': typecheck_cTup
}
interp = interp_Llambda.InterpLlambda().interp
interpX86 = interp_x86
interp_dict = {
    'remove_complex_operands': interp,
    # 'prelude_and_conclusion': interp_x86,
}

if False:
    run_tests('var', compiler, 'var',
              typecheck_dict,
              interp_dict)
else:
    run_one_test(os.getcwd() + '/tests/var/zero.py',
                 'var',
                 compiler,
                 'var',
                 typecheck_dict,
                 interp_dict)

