# The solution is heavily inspired by the ones provided by Stephan Mennicke.

from z3 import *

# takes width and height of a single block, e.g. 3 and 3 for a standard 9x9 sudoku
# returns a solver instance with the sudoku rules encoded and a three-dimensional array with propositional atoms (row, column, number)
def create_empty_sudoku(block_width, block_height):
    dimension = block_width * block_height

    atom_array = [[[Bool(f"p_{z}_{i},{j}") for z in range(dimension)] for j in range(dimension)] for i in range(dimension)]

    solver = Solver()

    # at least one value per cell
    solver.add(And([Or(atom_array[i][j]) for i in range(dimension) for j in range(dimension)]))

    # at most one value per cell
    solver.add(And([Not(And(atom_array[i][j][z1], atom_array[i][j][z2])) for i in range(dimension) for j in range(dimension) for z1 in range(dimension) for z2 in range(z1+1, dimension)]))
    
    # values different within each row
    solver.add(And([Not(And(atom_array[i][j1][z], atom_array[i][j2][z])) for i in range(dimension) for j1 in range(dimension) for j2 in range(j1+1, dimension) for z in range(dimension)]))

    # values different within each column
    solver.add(And([Not(And(atom_array[i1][j][z], atom_array[i2][j][z])) for i1 in range(dimension) for i2 in range(i1+1, dimension) for j in range(dimension) for z in range(dimension)]))

    # values different within each block
    for block_vert_offset in range(0, dimension, block_height):
        for block_horiz_offset in range(0, dimension, block_width):
            for i1 in range(block_height):
                for i2 in range(block_height):
                    for j1 in range(block_width):
                        for j2 in range(block_width):
                            if i1 == i2 and j1 == j2: continue
                            solver.add(And([Not(And(atom_array[block_vert_offset + i1][block_horiz_offset + j1][z], atom_array[block_vert_offset + i2][block_horiz_offset + j2][z])) for z in range(dimension)]))

    return (solver, atom_array)

# prints a solution if the sudoku admits a solution given a partial input (where 0 denotes no value, and 1 to dimension prefilled values (+1))
def print_solution(solver_with_rules, atom_array, partial_input):
    dimension = len(atom_array)
    solver_with_rules.push()

    # apply partial input
    solver_with_rules.add(And([atom_array[i][j][partial_input[i][j]-1] for i in range(dimension) for j in range(dimension) if partial_input[i][j] > 0]))

    if solver_with_rules.check() == sat:
        model = solver_with_rules.model()
        print_matrix = []
        for i in range(dimension):
            row = []
            for j in range(dimension):
                for z in range(dimension):
                    if model[atom_array[i][j][z]]:
                        row.append(z+1)
            print_matrix.append(row)

        print("Solution:")
        for row in print_matrix: 
            print(row)
    else:
        print("No solution.")

    solver_with_rules.pop()

# generate any sudoku and find solution
(solver, atom_array) = create_empty_sudoku(4,5)
print_solution(solver, atom_array, [[0 for j in range(4*5)] for i in range(4*5)])

# use pre-filled sudoku
pre_filled = [
  [0,0,3,0,0,0,0,0,0],
  [0,0,0,1,3,0,7,0,0],
  [6,1,0,0,9,0,0,0,0],

  [2,0,1,0,0,8,0,0,7],
  [0,0,6,0,2,0,4,0,0],
  [5,0,0,9,0,0,1,0,3],

  [0,0,0,0,4,0,0,8,6],
  [0,0,5,0,8,7,0,0,0],
  [0,0,0,0,0,0,9,0,0],
]
(solver, atom_array) = create_empty_sudoku(3,3)
print_solution(solver, atom_array, pre_filled)

