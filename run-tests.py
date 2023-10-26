import os
import sys

sys.path.append('../python-student-support-code')
sys.path.append('../python-student-support-code/interp_x86')

import compiler
import interp_Lvar
import type_check_Lvar
import interp_Ltup
import type_check_Ltup
from utils import run_tests, run_one_test, enable_tracing
from interp_x86.eval_x86 import interp_x86

enable_tracing()

compiler = compiler.Compiler()

typecheck = type_check_Ltup.TypeCheckLtup().type_check

typecheck_dict = {
    'source': typecheck,
    'shrink': typecheck,
    'remove_complex_operands': typecheck,
}
interp = interp_Ltup.InterpLtup().interp
interp_dict = {
    'remove_complex_operands': interp,
    'select_instructions': interp_x86,
    'assign_homes': interp_x86,
    'patch_instructions': interp_x86,
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

