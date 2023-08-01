import csp
import itertools
import time
import sys

class KenKen(csp.CSP):
    """
    The KenKen Problem.
    Example execution:
    python kenken.py    [inputFile.txt]

    inputFile formatting:  
        row 1       The size of the kenken grid of the problem (3 <= size <= 9)
        row 2 .. n  Strings that constitute a BLOCK of possibly many variables (cells)
                    goal Value [%] Cell-Cell-Cell..-Cell [%] Operation to be used
                    where Cell is the ascending number of the cell
                    e.g. if size = 4
                    0 -> cage (0,0)     1-> cage(0,1)   2->cage(0,2)    3->cage(0,3)
                    4 -> cage (1,0)     5-> cage(1,1)   ...
    
    TO CHECK THE SOLUTION:
        Call s.assertSolution(solution, output)
            Solution must be a text file with the same name as the file given for input,
            with a "-Solution" extension before .txt

                e.g. inputFile = "K4.txt"   then the solution's text file name: "K4-Solution.txt"
                
            If output is True, we also print the solution in grid-like readable form 

        Formatting for solutions:
            A grid-like form, each row represents the row in the KenKen solution 
            Values seperated using spaces and using a new line to enter the next row

            e.g.
            3 2 4 1 
            4 1 3 2 
            2 4 1 3 
            1 3 2 4 

    """

    def __init__(self,size, lines):
        """
            A tuple of three strings is passed as argument.
            The first string of the tupple, indicates the cage of each cell.
            The second and the third string show the goal number and the operation of each cage respectively.
        """
        self.numOfCages = len(lines)
        self.n = n = size
        self.cage = {}  # dictionary that maps the position of a block to a cage
        self.cageGoal = {}   # dictionary that maps a cage with an operation and goal value
        self.domain = {}
        self.neighbors = {}
        self.variables = range(self.numOfCages)

        # blocks is the reverse, mapping a cage to a position of a block
        self.blocks = {}
        [self.blocks.setdefault(x,[]) for x in range(len(lines))]
        
        self._defVariables(lines)
        
        self._defDomain()

        self._defNeigh()


        csp.CSP.__init__(self,self.variables, self.domain, self.neighbours, self.kenkenConstraint)

    def _defVariables(self,lines):
        """
            Function to define the variables of the KenKen
            As a variable we define a block/group of cells
            NOT a individual cell
        """
        for i in range(len(lines)):
            # the new line consists of: 
            # val   : the desired goal value
            # #
            # var   : the variables seperated by -
            # #
            # op    : the operation to be used (+,-,*,/,=)
            line = lines[i]

            # Split in 3 parts
            val, var, op = line.split('#')
            
            # Split the variables to get each seperately
            variablesInLine = var.split('-')
            op = op.replace("\n", '')   # for the trailing \n

            # Save: for block number i:    (Goal Value, Operation to be used)
            self.cageGoal[i] = ( int(val), op)


            for var in variablesInLine:
                # from the number, get the div and mod
                # which will show us the (row, column) form of cell
                x = int(var) / size
                y = int(var) % size

                # Now save that: (row, column) cage is part of block i
                self.cage[(int(x), int(y))] = i
                # And also save that part of block i, is the (row,column) cell
                self.blocks[i].append( (int(x), int(y)) )
        
    def _defDomain(self):
        """
            Function to define the domain of the variables
            Not that easy, since a variable consists of many individual cells
        """
        
        cellDomain = [ n for n in range(1,self.n+1)]  # Cell's value can be 1,2,...,n

        for i in range(self.numOfCages):
            # Get all possible permutations of the cells inside the block
            # i.e. all assignments possible of the individual cells inside the block
            # For that we need to set repeat= number of variables in block
            # e.g. if n = 3 and we have two cells inside the block
            # all assignments are = [(1,1,1), (1,1,2), (1,1,3),(2,1,1), ... (3,3,3)]

            perms = [perm for perm in itertools.product(cellDomain, repeat=len(self.blocks[i]))] 
            self.domain[i] = self.satAssignments(i,perms)

    def _defNeigh(self):
        """
            Function to define the neighbours of every variable
            Simply go through every cell checking  if in the same row or in the same column
            Exists a cell that belongs to another block of cells
        """
        # Initialize the neighbours
        self.neighbours = {}
        [self.neighbours.setdefault(x,[]) for x in range(self.numOfCages)]

        for block in range(self.numOfCages):
            for (x,y) in self.blocks[block]:
                for grid_i in range(self.n):
                    if self.cage[(grid_i,y)] != block and self.cage[(grid_i,y)] not in self.neighbours[block]:
                        self.neighbours[block].append(self.cage[(grid_i,y)])
                    if self.cage[(x,grid_i)] != block and self.cage[(x,grid_i)] not in self.neighbours[block]:
                        self.neighbours[block].append(self.cage[(x,grid_i)])
        
    def kenkenConstraint(self, A, a, B, b):
        assignment = {}

        i = 0
        # Get every cell inside the block/group
        for (x,y) in self.blocks[A]:
            # Assign the value to that cell
            assignment[(x,y)] = a[i]
            i+=1
        
        i = 0
        for (x,y) in self.blocks[B]:
            assignment[(x,y)] = b[i]
            i+=1
        
        # Like doing two for loops, but a bit fancier
        perm = [ perm for perm in itertools.product(self.blocks[A], self.blocks[B]) ]

        for (assignment1, assignment2) in perm:
            (x1,y1) = assignment1
            (x2,y2) = assignment2
            # If the two points are on the same row OR column AND have the same value
            # The assignment is wrong, contraint not satisfied
            if assignment[(x1,y1)] == assignment[(x2,y2)] and (x1==x2 or y1==y2):
                return False
 
        return True

    def assertSolution(self, assignment, write = False):
        """
        Print assignment in a readable way
        """
        if assignment is None:
            return
        
        # Get the name of the file, before .txt extension
        seperated = sys.argv[1].split(".")
        sols = seperated[0] + "-Solution.txt"

        with open(sols, "r") as f:
            lines = f.readlines()[:]
        

        f.close()
        lines = [item.strip() for item in lines]

        # blockAssignment is a dictionary that maps a position to its value according to the assignment
        blockAssignment = {}
        for cage in range(self.numOfCages):
            i = 0
            for (x,y) in self.blocks[cage]:
                blockAssignment[(x,y)] = assignment[cage][i]
                i += 1

        try:
            # Go through the nxn grid
            for x in range(self.n):
                solutionLine = lines[x]
                solutionLine = solutionLine.split() # split using spaces to get numbers in row x
                for y in range(self.n):
                    assert blockAssignment[(x,y)] == int(solutionLine[y])
                    if write == True:
                        print(blockAssignment[(x,y)],end=' ')
                if write == True:
                    print()
            print("Solution: Correct", u'\u2705')
        except:
            print("Solution: Fail", u'\u274C')

    
    def satAssignments(self,block,permutationsOfValues):
        """
            block:  A block of cages/cells constiting of one or move values
            permutationsOfValues:  list of all possible values each cage of the block can get
        """
        operation = self.cageGoal[block][1]
        goalValue = self.cageGoal[block][0]
        satisfactoryAssignments = []

        for assignments in permutationsOfValues:
            if operation == '=':
                if assignments[0] == goalValue:
                    satisfactoryAssignments.append(assignments)
                    continue
            if operation == '+':
                if sum(assignments) == goalValue:
                    satisfactoryAssignments.append(assignments)
                continue
            if operation == '-':
                if assignments[1] - assignments[0] == goalValue or assignments[0] - assignments[1] == goalValue:
                    satisfactoryAssignments.append(assignments)
                continue
            if operation == '*':
                product = 1

                for assignment in assignments:
                    product *=assignment
                
                if product == goalValue:
                    satisfactoryAssignments.append(assignments)
                continue
            if operation == '/':
                if assignments[0] != 0 and assignments[1]!=0:
                    if  assignments[0] / assignments[1] == goalValue or assignments[1] / assignments[0] == goalValue:
                        satisfactoryAssignments.append(assignments)   
            
        return satisfactoryAssignments

if __name__ == '__main__':
    
    with open(sys.argv[1], "r") as f:
        lines = f.readlines()[:]
        size = int(lines[0])
        lines = lines[1:]
    
    f.close()

    choose = [1,2,3,4,5,6]

    with open('results.txt', 'w') as f:
        f.write("N \t Time \t Assignments\n")
        for choice in choose:

            s = KenKen(size, lines)

            if choice == 1:
                print("BT")
                f.write("BT\t")
                start_time = time.time()
                a = csp.backtracking_search(s)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                s.assertSolution(a, False)
                f.write('\n')
                continue
            elif choice == 2:
                print("FC")
                f.write("FC\t")
                start_time = time.time()
                a = csp.backtracking_search(s, inference=csp.forward_checking)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                f.write('\n')
                s.assertSolution(a, False)
                continue

            elif choice == 3:
                print("MAC")
                f.write("MAC\t")
                start_time = time.time()
                a = csp.backtracking_search(s, inference=csp.mac)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                f.write('\n')
                
                s.assertSolution(a, False)
                continue

            elif choice == 4:
                print("BT + MRV")
                f.write("BT + MRV\t")
                start_time = time.time()
                a = csp.backtracking_search(s, select_unassigned_variable=csp.mrv)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                f.write('\n')
                s.assertSolution(a, False)
                continue

            elif choice == 5:
                print("FC + MRV")
                f.write("FC + MRV\t")
                start_time = time.time()
                a = csp.backtracking_search(s, select_unassigned_variable=csp.mrv ,inference=csp.forward_checking)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                f.write('\n')
                
                s.assertSolution(a, False)
                continue

            elif choice == 6:
                print("MAC + MRV")
                f.write("MAC + MRV\t")
                start_time = time.time()
                a = csp.backtracking_search(s, select_unassigned_variable=csp.mrv ,inference=csp.mac)
                f.write(str((time.time() - start_time)) + "\t" + str(s.nassigns))
                s.assertSolution(a, False)
                continue

            elif choice == 7:
                print("MIN-CONFICTS")
                start_time = time.time()
                a = csp.min_conflicts(s)
                print("> MIN-CONFICTS | Time = " + str((time.time() - start_time)) + " | Assigns = " + str(s.nassigns))
                s.assertSolution(a, False)

    f.close()