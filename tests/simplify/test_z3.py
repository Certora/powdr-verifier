import z3

def test_z3_solve_eqs():
    a = z3.Int('a')
    b = z3.Int('b')
    f = a == b*b - 3

    tactic = z3.Then('simplify', 'solve-eqs')
    goal = z3.Goal()
    goal.add(f)
    result = tactic(goal)
    print(f'result: {result}')

    s = z3.Solver()
    s.add(result[0])
    print(f'check: {s.check()}')
    print(f'model: {s.model()}')
    print(result[0].convert_model(s.model()))

    #import IPython; IPython.embed()

    #s = z3.Solver()
    #for r in result:
    #    s.add(r)
    #s.check()
    #model = s.model()
    #print(f'model: {model}')

    #print(goal.convert_model(model))
