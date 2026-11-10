"""wrapper around scripts/forty/gen.py that widens the numeric check window of ecs.theta_series"""
import sys, ast
sys.path.insert(0, '/Users/thomasdifiore/RamanujanTau/scripts/forty')
import ecs
ecs.theta_series.__defaults__ = (120, 6000)
import gen
tag = sys.argv[1]
form = ast.literal_eval(sys.argv[2]); s1 = ast.literal_eval(sys.argv[3]); s2 = ast.literal_eval(sys.argv[4])
print(gen.gen_typeII(tag, form, s1, s2))
