import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import interp_Lvar
import type_check_Lvar
import interp_Ltup
import type_check_Ltup
import type_check_Ctup
import type_check_Larray
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

typecheck = type_check_Ltup.TypeCheckLtup().type_check

typecheck_cTup = type_check_Ctup.TypeCheckCtup().type_check

typecheck_dict = {
    'source': typecheck,
    'shrink': typecheck,
    'expose_allocation': typecheck,
    'remove_complex_operands': typecheck,
    'explicate_control': typecheck_cTup,
    'select_instructions': typecheck_cTup,
    'assign_homes': typecheck_cTup
}
interp = interp_Ltup.InterpLtup().interp
interp_dict = {
    'remove_complex_operands': interp
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

