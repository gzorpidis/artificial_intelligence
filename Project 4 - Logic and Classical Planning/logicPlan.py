# logicPlan.py
# ------------
# Licensing Information:  You are free to use or extend these projects for
# educational purposes provided that (1) you do not distribute or publish
# solutions, (2) you retain this notice, and (3) you provide clear
# attribution to UC Berkeley, including a link to http://ai.berkeley.edu.
# 
# Attribution Information: The Pacman AI projects were developed at UC Berkeley.
# The core projects and autograders were primarily created by John DeNero
# (denero@cs.berkeley.edu) and Dan Klein (klein@cs.berkeley.edu).
# Student side autograding was added by Brad Miller, Nick Hay, and
# Pieter Abbeel (pabbeel@cs.berkeley.edu).


"""
In logicPlan.py, you will implement logic planning methods which are called by
Pacman agents (in logicAgents.py).
"""

from re import T
from typing import Dict, List, Tuple, Callable, Generator, Any
import util
import sys
import logic
import game

from logic import conjoin, disjoin
from logic import PropSymbolExpr, Expr, to_cnf, pycoSAT, parseExpr, pl_true

import itertools
import copy

pacman_str = 'P'
food_str = 'FOOD'
wall_str = 'WALL'
pacman_wall_str = pacman_str + wall_str
ghost_pos_str = 'G'
ghost_east_str = 'GE'
pacman_alive_str = 'PA'
DIRECTIONS = ['North', 'South', 'East', 'West']
blocked_str_map = dict([(direction, (direction + "_blocked").upper()) for direction in DIRECTIONS])
geq_num_adj_wall_str_map = dict([(num, "GEQ_{}_adj_walls".format(num)) for num in range(1, 4)])
DIR_TO_DXDY_MAP = {'North':(0, 1), 'South':(0, -1), 'East':(1, 0), 'West':(-1, 0)}


#______________________________________________________________________________
# QUESTION 1

def sentence1() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    A or B
    (not A) if and only if ((not B) or C)
    (not A) or (not B) or C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = logic.Expr('A')
    B = logic.Expr('B')
    C = logic.Expr('C')
    a_or_b = logic.disjoin(A,B)
    only_if = (~A % (~B | C))
    not_a_not_b = logic.disjoin(~A, ~B, C)
    return logic.conjoin(a_or_b, only_if, not_a_not_b)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence2() -> Expr:
    """Returns a Expr instance that encodes that the following expressions are all true.
    
    C if and only if (B or D)
    A implies ((not B) and (not D))
    (not (B and (not C))) implies A
    (not D) implies C
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = logic.Expr('A')
    B = logic.Expr('B')
    C = logic.Expr('C')
    D = logic.Expr('D')
    c_if = C % (B | D)
    a_implies = A >> (~B & ~D)
    not_clause = ~(B & ~C) >> A
    not_implies = ~D >> C
    return logic.conjoin(c_if, a_implies, not_clause, not_implies)
    # util.raiseNotDefined()
    "*** END YOUR CODE HERE ***"


def sentence3() -> Expr:
    """Using the symbols PacmanAlive_1 PacmanAlive_0, PacmanBorn_0, and PacmanKilled_0,
    created using the PropSymbolExpr constructor, return a PropSymbolExpr
    instance that encodes the following English sentences (in this order):

    Pacman is alive at time 1 if and only if Pacman was alive at time 0 and it was
    not killed at time 0 or it was not alive at time 0 and it was born at time 0.

    Pacman cannot both be alive at time 0 and be born at time 0.

    Pacman is born at time 0.
    (Project update: for this question only, [0] and _t are both acceptable.)
    """
    "*** BEGIN YOUR CODE HERE ***"
    A = logic.Expr('PacmanAlive_1')
    B= logic.Expr('PacmanAlive_0')
    C = logic.Expr('PacmanBorn_0')
    D = logic.Expr('PacmanKilled_0')

    pacman_alive = A % ((B&~D) | (~B&C))
    pacman_not_alive = ~(B&C)
    pacman_born = C


    return logic.conjoin(pacman_alive,pacman_not_alive, pacman_born)
 
    "*** END YOUR CODE HERE ***"

def findModel(sentence: Expr) -> Dict[Expr, bool]:
    """Given a propositional logic sentence (i.e. a Expr instance), returns a satisfying
    model if one exists. Otherwise, returns False.
    """
    cnf_sentence = to_cnf(sentence)
    return pycoSAT(cnf_sentence)

def findModelCheck() -> Dict[Any, bool]:
    """Returns the result of findModel(Expr('a')) if lower cased expressions were allowed.
    You should not use findModel or Expr in this method.
    This can be solved with a one-line return statement.
    """
    class dummyClass:
        """dummy('A') has representation A, unlike a string 'A' that has repr 'A'.
        Of note: Expr('Name') has representation Name, not 'Name'.
        """
        def __init__(self, variable_name: str = 'A'):
            self.variable_name = variable_name
        
        def __repr__(self):
            return self.variable_name
    "*** BEGIN YOUR CODE HERE ***"
    
    return {dummyClass('a') :True}
 
    "*** END YOUR CODE HERE ***"

def entails(premise: Expr, conclusion: Expr) -> bool:
    """Returns True if the premise entails the conclusion and False otherwise.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # φ |= ψ <-> (φ ΚΑΙ ΟΧΙ(ψ)) είναι μη ικανοποιήσιμη
    # Άρα αν επιστρέψει False, τότε το κάνει entail
    return not findModel(premise & ~ conclusion)
    "*** END YOUR CODE HERE ***"

def plTrueInverse(assignments: Dict[Expr, bool], inverse_statement: Expr) -> bool:
    """Returns True if the (not inverse_statement) is True given assignments and False otherwise.
    pl_true may be useful here; see logic.py for its description.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # Since we want to return True if the not inverse is True, simply
    # Use the already implemented "pl_true" function
    # but with the inverse expression/statement as input
    return pl_true(~inverse_statement, assignments) 
    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 2

def atLeastOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals (i.e. in the form A or ~A), return a single 
    Expr instance in CNF (conjunctive normal form) that represents the logic 
    that at least one of the literals ist is true.
    >>> A = PropSymbolExpr('A');
    >>> B = PropSymbolExpr('B');
    >>> symbols = [A, B]
    >>> atleast1 = atLeastOne(symbols)
    >>> model1 = {A:False, B:False}
    >>> print(pl_true(atleast1,model1))
    False
    >>> model2 = {A:False, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    >>> model3 = {A:True, B:True}
    >>> print(pl_true(atleast1,model2))
    True
    """
    "*** BEGIN YOUR CODE HERE ***"
    # We have it ready!
    return logic.disjoin(literals)
    "*** END YOUR CODE HERE ***"


def atMostOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form) that represents the logic that at most one of 
    the expressions in the list is true.
    itertools.combinations may be useful here.
    """
    "*** BEGIN YOUR CODE HERE ***"
    cnf = list()

    # (N choose 2)
    # An example to understand the formula
    # - ( (l1 AND l2) or (l2 AND l3) or (l3 AND l1) )
    # (-l1 OR -l2) AND (-l2 OR -l3) AND (-l3 OR -l1)
    combs = itertools.combinations(literals,2)
    for lektiko1,lektiko2 in combs:
            if lektiko1 != lektiko2:
                cnf.append(~lektiko1 | ~lektiko2)
    
    return logic.conjoin(cnf)
    "*** END YOUR CODE HERE ***"


def exactlyOne(literals: List[Expr]) -> Expr:
    """
    Given a list of Expr literals, return a single Expr instance in 
    CNF (conjunctive normal form)that represents the logic that exactly one of 
    the expressions in the list is true.
    """
    "*** BEGIN YOUR CODE HERE ***"
    # If at least one is true, and at most one is true, then exactly one must be true

    return logic.conjoin(atLeastOne(literals), atMostOne(literals))
    "*** END YOUR CODE HERE ***"
    
    

#______________________________________________________________________________
# QUESTION 3

def pacmanSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]=None) -> Expr:
    """
    Successor state axiom for state (x,y,t) (from t-1), given the board (as a 
    grid representing the wall locations).
    Current <==> (previous position at time t-1) & (took action to move to x, y)
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    """
    
    now, last = time, time - 1
    possible_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t
    # the if statements give a small performance boost and are required for q4 and q5 correctness

    if walls_grid[x][y+1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        possible_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not possible_causes:
        return None
    
    "*** BEGIN YOUR CODE HERE ***"
    # Use PropSymbolExpr to express Pacman being at [x,y] at time t
    # <-> Pacman was at a position at time t-1, and took a step (out of those available)
    current =  PropSymbolExpr(pacman_str, x, y, time=now) 
    return current % logic.disjoin(possible_causes)


def SLAMSuccessorAxiomSingle(x: int, y: int, time: int, walls_grid: List[List[bool]]) -> Expr:
    """
    Similar to `pacmanSuccessorStateAxioms` but accounts for illegal actions
    where the pacman might not move timestep to timestep.
    Available actions are ['North', 'East', 'South', 'West']
    """
    now, last = time, time - 1
    moved_causes: List[Expr] = [] # enumerate all possible causes for P[x,y]_t, assuming moved to having moved
    if walls_grid[x][y+1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y+1, time=last)
                            & PropSymbolExpr('South', time=last))
    if walls_grid[x][y-1] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x, y-1, time=last) 
                            & PropSymbolExpr('North', time=last))
    if walls_grid[x+1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x+1, y, time=last) 
                            & PropSymbolExpr('West', time=last))
    if walls_grid[x-1][y] != 1:
        moved_causes.append( PropSymbolExpr(pacman_str, x-1, y, time=last) 
                            & PropSymbolExpr('East', time=last))
    if not moved_causes:
        return None

    moved_causes_sent: Expr = conjoin([~PropSymbolExpr(pacman_str, x, y, time=last) , ~PropSymbolExpr(wall_str, x, y), disjoin(moved_causes)])

    failed_move_causes: List[Expr] = [] # using merged variables, improves speed significantly
    auxilary_expression_definitions: List[Expr] = []
    for direction in DIRECTIONS:
        dx, dy = DIR_TO_DXDY_MAP[direction]
        wall_dir_clause = PropSymbolExpr(wall_str, x + dx, y + dy) & PropSymbolExpr(direction, time=last)
        wall_dir_combined_literal = PropSymbolExpr(wall_str + direction, x + dx, y + dy, time=last)
        failed_move_causes.append(wall_dir_combined_literal)
        auxilary_expression_definitions.append(wall_dir_combined_literal % wall_dir_clause)

    failed_move_causes_sent: Expr = conjoin([
        PropSymbolExpr(pacman_str, x, y, time=last),
        disjoin(failed_move_causes)])

    return conjoin([PropSymbolExpr(pacman_str, x, y, time=now) % disjoin([moved_causes_sent, failed_move_causes_sent])] + auxilary_expression_definitions)


def pacphysicsAxioms(t: int, all_coords: List[Tuple], non_outer_wall_coords: List[Tuple], walls_grid: List[List] = None, sensorModel: Callable = None, successorAxioms: Callable = None) -> Expr:
    """
    Given:
        t: timestep
        all_coords: list of (x, y) coordinates of the entire problem
        non_outer_wall_coords: list of (x, y) coordinates of the entire problem,
            excluding the outer border (these are the actual squares pacman can
            possibly be in)
        walls_grid: 2D array of either -1/0/1 or T/F. Used only for successorAxioms.
            Do NOT use this when making possible locations for pacman to be in.
        sensorModel(t, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
        successorAxioms(t, walls_grid, non_outer_wall_coords) -> Expr: function that generates
            the sensor model axioms. If None, it's not provided, so shouldn't be run.
    Return a logic sentence containing all of the following:
        - for all (x, y) in all_coords:
            If a wall is at (x, y) --> Pacman is not at (x, y)
        - Pacman is at exactly one of the squares at timestep t.
        - Pacman takes exactly one action at timestep t.
        - Results of calling sensorModel(...), unless None.
        - Results of calling successorAxioms(...), describing how Pacman can end in various
            locations on this time step. Consider edge cases. Don't call if None.
    """
    """
    Arguments:
    Required: t = time, all_coords and non_outer_wall_coords are lists of (x, y) tuples.
    Possibly-None: You will be using these to call functions, not much logic is required.
    walls_grid is only passed through to successorAxioms and describes (known) walls.
    sensorModel(t: int, non_outer_wall_coords) -> Expr returns a single Expr describing observation rules; you can take a look at sensorAxioms and SLAMSensorAxioms to see examples of this.
    successorAxioms(t: int, walls_grid, non_outer_wall_coords) -> Expr describes transition rules, e.g. how previous locations and actions of Pacman affect the current location; 
    we have seen this in the functions in the previous bullet point.
    Algorithm:
    For all (x, y) in all_coords, append the following implication (if-then form): if a wall is at (x, y), then Pacman is not at (x, y) at t.
    Pacman is at exactly one of the non_outer_wall_coords at timestep t.
    Pacman takes exactly one of the four actions in DIRECTIONS at timestep t.
    Sensors: append the result of sensorAxioms. All callers except for checkLocationSatisfiability make use of this; how to handle the case where we don't want any sensor axioms added is up to you.
    Transitions: append the result of successorAxioms. All callers will use this.
    Add each of the sentences above to pacs_prop_sentences. As you can see in the return statement, these will be conjoined and returned.
    Function passing syntax:
    Let def myFunction(x, y, t): return PropSymbolExpr('hello', x, y, time=t) be a function we want to use.
    Let def myCaller(func: Callable): ... be the caller that wants to use a function.
    We can pass the function in: myCaller(myFunction) (note that myFunction is not called with () after it).
    We can use myFunction by having inside myCaller this: useful_return = func(0, 1, q).
    """
    """
    Reminder: 
    the variable for whether Pacman is at (x, y) at time t is 
    PropSymbolExpr(pacman_str, x, y, time=t), 
    wall exists at (x, y) is PropSymbolExpr(wall_str, x, y, time=t), 
    and action is taken at t is PropSymbolExpr(action, time=t).
    """
    pacs_prop_sentences = []
    
    
    "*** BEGIN YOUR CODE HERE ***"
    actions = []
    pacman_p_pos = []

    #   (1) For all (x, y) in all_coords, append the following implication (if-then form): 
    # if a wall is at (x, y), then Pacman is not at (x, y) at t.
    for x,y in all_coords:
        # So simply enough, if WALL[x][y] -> not (PACMAN[x][y] at t)
        pacs_prop_sentences.append(PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(pacman_str, x, y, time=t))


    #   (2) Pacman is at exactly one of the non_outer_wall_coords at timestep t.
    for x,y in non_outer_wall_coords:
        pacman_p_pos.append(PropSymbolExpr(pacman_str, x, y, time=t))
    print(pacman_p_pos)
    # Now we have a list of all possible positions of the pacman

    # Create expression to depict that out of all the possible positions
    # the pacman can only be at one of these
    pacs_prop_sentences.append(exactlyOne(pacman_p_pos))

    #   (3) Pacman takes exactly one of the four actions in DIRECTIONS at timestep t.
    
    for dir in DIRECTIONS:
        actions.append(PropSymbolExpr(dir, time=t))
    pacs_prop_sentences.append(exactlyOne(actions))

    #   (4)  append the result of sensorAxioms.    
    if sensorModel is not None:
        pacs_prop_sentences.append(sensorModel(t, non_outer_wall_coords))
    
    #   (5)  append the result of successorAxioms  
    # describes transition rules, e.g. how previous locations and actions of Pacman affect the current location; 
    # so t has to be greater than 0, so a previous action and location exists

    if successorAxioms and t != 0:
        pacs_prop_sentences.append(successorAxioms(t, walls_grid, non_outer_wall_coords))

    return conjoin(pacs_prop_sentences)


def checkLocationSatisfiability(x1_y1: Tuple[int, int], x0_y0: Tuple[int, int], action0, action1, problem):
    """
    Given:
        - x1_y1 = (x1, y1), a potential location at time t = 1
        - x0_y0 = (x0, y0), Pacman's location at time t = 0
        - action0 = one of the four items in DIRECTIONS, Pacman's action at time t = 0
        - action1 = to ensure match with autograder solution
        - problem = an instance of logicAgents.LocMapProblem
    Note:
        - there's no sensorModel because we know everything about the world
        - the successorAxioms should be allLegalSuccessorAxioms where needed
    Return:
        - a model where Pacman is at (x1, y1) at time t = 1
        - a model where Pacman is not at (x1, y1) at time t = 1
    """

    """

    Given a transition (x0_y0, action0, x1_y1), action1, and a problem, 
    you will write a function that will return a tuple of two models (model1, model2).
    In model1, Pacman is at (x1, y1) at time t = 1 given x0_y0, action0, action1, proving that it's possible that Pacman there. 
    Notably, if model1 is False, we know Pacman is guaranteed to NOT be there.
    In model2, Pacman is NOT at (x1, y1) at time t = 1 given x0_y0, action0, action1, proving that it's possible that Pacman is not there. 
    Notably, if model2 is False, we know Pacman is guaranteed to be there.
    action1 has no effect on determining whether the Pacman is at the location; it's there just to match your solution to the autograder solution.
    To implement this problem, you will need to add the following expressions to your KB:
    Add to KB: pacphysics_axioms(...) with the appropriate timesteps. There is no sensorModel because we know everything about the world. Where needed, use allLegalSuccessorAxioms for transitions since this is for regular Pacman transition rules.
    Add to KB: Pacman’s current location (x0, y0)
    Add to KB: Pacman takes action0
    Add to KB: Pacman takes action1
    Query the SAT solver with findModel for two models described earlier. The queries should be different; for a reminder on how to make queries see entails.
    
    """
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))
    KB = []
    x0, y0 = x0_y0
    x1, y1 = x1_y1

    # We know which coords are walls:
    map_sent = [PropSymbolExpr(wall_str, x, y) for x, y in walls_list]
    KB.append(conjoin(map_sent))

    "*** BEGIN YOUR CODE HERE ***"
    #   (1) Add to KB: pacphysics_axioms(...) with the appropriate timesteps. 
    # Appropriate timesteps: t = 0, t = 1
    for t in range(2):
        pac_t = pacphysicsAxioms(t, all_coords, non_outer_wall_coords)
        KB.append(pac_t)

    # successorAxioms needed: for t = 1
    KB.append(allLegalSuccessorAxioms(1,walls_grid, non_outer_wall_coords))
    
    #   (2) Add to KB: Pacman’s current location (x0, y0)
    KB.append(PropSymbolExpr(pacman_str, x0, y0, time=0))

    #   (3) Add to KB: Pacman takes action0, Add to KB: Pacman takes action1
    for t in range(2):
        if t == 0:
            pac_action_t = PropSymbolExpr(action0, time=t)
        else:
            pac_action_t = PropSymbolExpr(action1, time=t)
        KB.append(pac_action_t)

    # Query
    query = PropSymbolExpr(pacman_str, x1, y1, time=1)
    
    #model1: Pacman is at (x1, y1) at time t = 1 so there is a possiblity Pacman is there 
    #model2: Pacman is NOT at (x1, y1) at time t = 1 so there is a possibility Pacman is not there
    # if model1: false -> NOT THERE
    # if model2: false -> THERE
    
    return (
        findModel(conjoin(KB) & query),  # model1
        findModel(conjoin(KB) & ~query)  # model2
        )



    "*** END YOUR CODE HERE ***"

#______________________________________________________________________________
# QUESTION 4

def positionLogicPlan(problem) -> List:
    """
    Given an instance of a PositionPlanningProblem, return a list of actions that lead to the goal.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    """
    Add to KB: Initial knowledge: Pacman's initial location at timestep 0
    for t in range(50) [Autograder will not test on layouts requiring ≥ 50 timesteps]
    Print time step; this is to see that the code is running and how far it is.
    Add to KB: Initial knowledge: Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t. 
    This is similar to pacphysicsAxioms, but don't use that method since we are using non_wall_coors 
    when generating the list of possible locations in the first place (and walls_grid later).
    Is there a satisfying assignment for the variables given the knowledge base so far? 
    Use findModel and pass in the Goal Assertion and KB.
    If there is, return a sequence of actions from start to goal using extractActionSequence.
    Here, Goal Assertion is the expression asserting that Pacman is at the goal at timestep t.
    Add to KB: Pacman takes exactly one action per timestep.
    Add to KB: Transition Model sentences: call pacmanSuccessorAxiomSingle(...) for all possible pacman positions in non_wall_coords.
    """
    walls_grid = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls_grid.asList()
    x0, y0 = problem.startState
    xg, yg = problem.goal
    
    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), 
            range(height + 2)))
    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]
    KB = []
    

    "*** BEGIN YOUR CODE HERE ***"
    #Add to KB: Initial knowledge: Pacman's initial location at timestep 0
    pacman_location0 = PropSymbolExpr(pacman_str, x0, y0, time=0)
    KB.append(pacman_location0)

    for t in range(50):
        possible_locations = []
        directions = []
        #   (1) printing timesteps to prove slowness
        print(t)   

    
        #   (2) Add to KB: 
        # Initial knowledge: 
        for x,y in non_wall_coords:
            # All possible positions for time = t, get all of them and then we will
            # apply exactlyOne
            possible_locations.append(PropSymbolExpr(pacman_str, x, y, time=t))
            
            # If there is a wall at [x][y] pacman can't be there
            KB.append(PropSymbolExpr(wall_str, x, y) >> ~PropSymbolExpr(pacman_str, x, y, time=t))
        

        # Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t.
        KB.append(exactlyOne(possible_locations))

        #   (4) Add to KB: Pacman takes exactly one action per timestep.
        for dir in actions:
            directions.append(PropSymbolExpr(dir, time=t))
        KB.append(exactlyOne(directions))

        #   (5) Add to KB: Transition Model sentences: call pacmanSuccessorAxiomSingle(...) for all possible pacman positions in non_wall_coords.
        if t != 0:
            for x,y in non_wall_coords:
                KB.append(pacmanSuccessorAxiomSingle(x, y, t, walls_grid))

        #Here, Goal Assertion is the expression asserting that Pacman is at the goal at timestep t.
        goal_query = PropSymbolExpr(pacman_str, xg, yg, time=t)

        # If a model is found, then we can extract the action sequence
        if findModel(conjoin(KB) & goal_query) != False:
            return extractActionSequence(findModel(conjoin(KB) & goal_query), actions)

#______________________________________________________________________________
# QUESTION 5

def foodLogicPlan(problem) -> List:
    """
    Given an instance of a FoodPlanningProblem, return a list of actions that help Pacman
    eat all of the food.
    Available actions are ['North', 'East', 'South', 'West']
    Note that STOP is not an available action.
    Overview: add knowledge incrementally, and query for a model each timestep. Do NOT use pacphysicsAxioms.
    """
    """
    What you will change from the previous question:

    Initialize Food[x,y]_t variables with the code PropSymbolExpr(food_str, x, y, time=t), 
    where each variable is true if and only if there is a food at (x, y) at time t.

    Change the goal assertion: Your goal assertion sentence must be true if and only if all of the food have been eaten. 
    This happens when all Food[x,y]_t are false.

    Add a food successor axiom: What is the relation between Food[x,y]_t+1 and Food[x,y]_t and Pacman[x,y]_t? 
    The food successor axiom should only involve these three variables, for any given (x, y) and t. 
    Think about what the transition model for the food variables looks like, and add these sentences to your knowledge base at each timestep.
    """
    walls = problem.walls
    width, height = problem.getWidth(), problem.getHeight()
    walls_list = walls.asList()
    (x0, y0), food = problem.start
    food = food.asList()

    # Get lists of possible locations (i.e. without walls) and possible actions
    all_coords = list(itertools.product(range(width + 2), range(height + 2)))

    non_wall_coords = [loc for loc in all_coords if loc not in walls_list]
    actions = [ 'North', 'South', 'East', 'West' ]

    KB = []
    
    
    "*** BEGIN YOUR CODE HERE ***"
    
    starting_loc = PropSymbolExpr(pacman_str, x0, y0, time=0)
    KB.append(starting_loc)
    
    #Add to KB: Initial knowledge: is there food at timestep 0
    for x,y in food:
        initial_food_points = PropSymbolExpr(food_str, x, y, time=0)
        KB.append(initial_food_points)
    
    for t in range(50):
        print(t)
        # Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t
        # So we must re initialize the list every time
        pac_position_at_t = []
        directions = []
        goal_state = []
        
        for action in DIRECTIONS:
            directions.append(PropSymbolExpr(action, time=t))
        KB.append(exactlyOne(directions))
        
        for x,y in non_wall_coords:
            # Add to KB: Initial knowledge: Pacman can only be at exactlyOne of the locations in non_wall_coords at timestep t.
            pac_position_at_t.append(PropSymbolExpr(pacman_str, x, y, time=t))
            # Add to KB: Transition Model sentences: call pacmanSuccessorAxiomSingle(...) for all possible pacman positions in non_wall_coords.
            KB.append(pacmanSuccessorAxiomSingle(x, y, time=t+1, walls_grid = walls))

        KB.append(exactlyOne(pac_position_at_t))
        
        for x,y in food:
            goal_state.append(PropSymbolExpr(food_str, x, y, time=t))
        
        # All foods point False: !F1 AND !F2 AND ... = !(F1 OR F2 OR ... Fi)
        goal_check = conjoin(conjoin(KB), ~disjoin(goal_state))
        if findModel(goal_check):
            return extractActionSequence(findModel(goal_check), actions)  

        # Food successor axiom:
        # If the pacman is at a position where a food is,
        # the an the next time (t+1) there won't be food there, since it will have been eaten
        for x,y in food:
            # If it was False before it stays false
            alreadyEaten = ~PropSymbolExpr(food_str, x, y, time=t)
            nowEaten = ~alreadyEaten & PropSymbolExpr(pacman_str, x, y, time=t)
            foodEaten = disjoin(alreadyEaten, nowEaten) % ~PropSymbolExpr(food_str, x, y, time=t+1)
            # if it's eaten -> FOOD[x][y]+t = False, alreadyEaten = True so the disjoin turns True, so alreadyEaten -> Turn it to eaten so FOOD[x][y]_t+1 = False
            # if it's not eaten -> FOOD[x][y]_t = True, alreadyEaten = False so not the disjoin depends on the position of the pacman
            KB.append(foodEaten)
#______________________________________________________________________________
# QUESTION 6

def localization(problem, agent) -> Generator:
    '''
    problem: a LocalizationProblem instance
    agent: a LocalizationLogicAgent instance
    '''
    walls_grid = problem.walls
    walls_list = walls_grid.asList()
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    KB = []

    "*** BEGIN YOUR CODE HERE ***"

    #   (1) Add to KB: where the walls are (walls_list) and aren't (not in walls_list)
    for x,y in all_coords:
        wall_exists = PropSymbolExpr(wall_str, x, y)
        # If (x,y) is in the walls_list
        if (x,y) in walls_list:
            # There is a wall there
            KB.append(wall_exists)
        else:
            # There is a NOT wall there  
            KB.append(~wall_exists)

    for t in range(agent.num_timesteps):
        possible_locations = []

        #   (2) Add pacphysics, 
        pacphysics = pacphysicsAxioms(t,all_coords, non_outer_wall_coords, walls_grid, sensorAxioms, allLegalSuccessorAxioms)
        # action,
        action = PropSymbolExpr(agent.actions[t], time=t)
        # and percept information to KB.
        perception = agent.getPercepts()
        info = fourBitPerceptRules(t, perception)

        KB.extend([pacphysics, action, info])

        #   (3) Find possible pacman locations with updated KB.
        for x,y in non_outer_wall_coords:

            locationAtTimeT = PropSymbolExpr(pacman_str,x, y, time=t)
            premise = conjoin(KB)
            pacAtXY = PropSymbolExpr(pacman_str,x, y, time=t)

            # Can we conclude from our current knowledge that pacman is at (x,y)?
            pacIsAtXY = entails(premise, pacAtXY)

            # Or that it's NOT at (x,y)?
            pacIsNotAtXY = entails(premise, ~pacAtXY)

            # if pacIsAtXY = False ->
            #   We can't conclude that pacman IS there, so it might not be!
            # if pacIsNotAtXy = False -> 
            #   We can't conclude that pacman is NOT there, so it might be!

            # pacman not being at XY is provable,
            # and we can't prove that it is at XY
            if pacIsNotAtXY and not pacIsAtXY:
                KB.append(~locationAtTimeT)
            # pacman at XY is provable
            # and we can't prove that it is not at XY
            elif pacIsAtXY and not pacIsNotAtXY:
                possible_locations.append((x,y))
                KB.append(locationAtTimeT)
            else:
                possible_locations.append((x,y))
     
        agent.moveToNextState(agent.actions[t])


        "*** END YOUR CODE HERE ***"
        yield possible_locations



#______________________________________________________________________________
# QUESTION 7

def mapping(problem, agent) -> Generator:
    '''
    problem: a MappingProblem instance
    agent: a MappingLogicAgent instance
    '''
    """
    Get initial location (pac_x_0, pac_y_0) of Pacman, and add this to KB. Also add whether there is a wall at that location.
    for t in range(agent.num_timesteps):
    Add pacphysics, action, and percept information to KB.
    Find provable wall locations with updated KB.
    Call agent.moveToNextState(action_t) on the current agent action at timestep t.yield known_map
    """
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # Pacman knows that the outer border of squares are all walls
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"

    #   (1) Get initial location (pac_x_0, pac_y_0) of Pacman, and add this to KB. Also add whether there is a wall at that location.
    starting_loc = PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time = 0)
    wall_at_start_loc = PropSymbolExpr(pacman_str, pac_x_0, pac_x_0, time=0) >> ~PropSymbolExpr(wall_str, pac_x_0, pac_y_0)
    
    KB.extend([starting_loc, wall_at_start_loc])

    for t in range(agent.num_timesteps):

        #   (2) Add pacphysics, 
        pacphysics = pacphysicsAxioms(t,all_coords, non_outer_wall_coords, known_map, sensorAxioms, allLegalSuccessorAxioms)
        # action,
        action = PropSymbolExpr(agent.actions[t], time=t)
        # and percept information to KB.
        perception = agent.getPercepts()
        info = fourBitPerceptRules(t, perception)

        KB.extend([pacphysics, action, info])

        #   (3) Find provable wall locations with updated KB.
        for x,y in non_outer_wall_coords:
            
            wallExistence = -1
            #Can we prove whether a wall is at (x, y)? Can we prove whether a wall is not at (x, y)? Use entails and the KB.
            wall = PropSymbolExpr(wall_str,x, y)
            premise = conjoin(KB)
            wallAtXY = PropSymbolExpr(wall_str,x, y)

            # Can we conclude from our current knowledge that pacman is at (x,y)?
            wallIsAtXY = entails(premise, wallAtXY)

            # Or that it's NOT at (x,y)?
            wallIsNotAtXY = entails(premise, ~wallAtXY)

            # if wallIsAtXY = False ->
            #   We can't conclude that wall IS there, so it might not be!
            # if wallIsNotAtXy = False -> 
            #   We can't conclude that wall is NOT there, so it might be!


            # wall not being at XY is provable,
            # and we can't prove that it is at XY
            if wallIsNotAtXY and not wallIsAtXY:
                KB.append(~wall)
                # 0 if (x, y) is guaranteed to not be a wall
                wallExistence = 0
            
            # wall at XY is provable
            # and we can't prove that it is not at XY
            elif wallIsAtXY and not wallIsNotAtXY:
                KB.append(wall)
                # 1 if (x, y) is guaranteed to be a wall at timestep t
                wallExistence = 1

            known_map[x][y] = wallExistence

            
        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        yield known_map

#______________________________________________________________________________
# QUESTION 8

def slam(problem, agent) -> Generator:
    '''
    problem: a SLAMProblem instance
    agent: a SLAMLogicAgent instance
    '''
    pac_x_0, pac_y_0 = problem.startState
    KB = []
    all_coords = list(itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)))
    non_outer_wall_coords = list(itertools.product(range(1, problem.getWidth()+1), range(1, problem.getHeight()+1)))

    # map describes what we know, for GUI rendering purposes. -1 is unknown, 0 is open, 1 is wall
    known_map = [[-1 for y in range(problem.getHeight()+2)] for x in range(problem.getWidth()+2)]

    # We know that the outer_coords are all walls.
    outer_wall_sent = []
    for x, y in all_coords:
        if ((x == 0 or x == problem.getWidth() + 1)
                or (y == 0 or y == problem.getHeight() + 1)):
            known_map[x][y] = 1
            outer_wall_sent.append(PropSymbolExpr(wall_str, x, y))
    KB.append(conjoin(outer_wall_sent))

    "*** BEGIN YOUR CODE HERE ***"

    starting_loc = PropSymbolExpr(pacman_str, pac_x_0, pac_y_0, time = 0)
    wall_at_start_loc = PropSymbolExpr(pacman_str, pac_x_0, pac_x_0, time=0) >> ~PropSymbolExpr(wall_str, pac_x_0, pac_y_0)
    KB.extend([starting_loc, wall_at_start_loc])
    known_map[pac_x_0][pac_y_0] = 0

    for t in range(agent.num_timesteps):
        possible_locations = []

        #   (2) Add pacphysics, 
        pacphysics = pacphysicsAxioms(t,all_coords, non_outer_wall_coords, known_map, SLAMSensorAxioms, SLAMSuccessorAxioms)
        # action,
        action = PropSymbolExpr(agent.actions[t], time=t)
        # and percept information to KB.
        perception = agent.getPercepts()
        info = numAdjWallsPerceptRules(t, perception)
        KB.extend([pacphysics, action, info])

        #Find provable wall locations with updated KB.        
        #Iterate over non_outer_wall_coords.
        for x,y in non_outer_wall_coords:

            # For info/comments regarding this, look at question 6
            locationAtTimeT = PropSymbolExpr(pacman_str,x, y, time=t)
            premise = conjoin(KB)
            pacAtXY = PropSymbolExpr(pacman_str,x, y, time=t)
            pacIsAtXY = entails(premise, pacAtXY)
            pacIsNotAtXY = entails(premise, ~pacAtXY)

            if pacIsNotAtXY and not pacIsAtXY:
                KB.append(~locationAtTimeT)
            elif pacIsAtXY and not pacIsNotAtXY:
                possible_locations.append((x,y))
                KB.append(locationAtTimeT)
            else:
                possible_locations.append((x,y))

            # For info/comments regarding this, look at question 7
            wallExistence = -1
            wall = PropSymbolExpr(wall_str,x, y)
            premise = conjoin(KB)
            wallAtXY = PropSymbolExpr(wall_str,x, y)
            wallIsAtXY = entails(premise, wallAtXY)
            wallIsNotAtXY = entails(premise, ~wallAtXY)
            if wallIsNotAtXY and not wallIsAtXY:
                KB.append(~wall)
                wallExistence = 0
            elif wallIsAtXY and not wallIsNotAtXY:
                KB.append(wall)
                wallExistence = 1

            known_map[x][y] = wallExistence

        #Call agent.moveToNextState(action_t) on the current agent action at timestep t
        agent.moveToNextState(agent.actions[t])
        "*** END YOUR CODE HERE ***"
        yield (known_map, possible_locations)


# Abbreviations
plp = positionLogicPlan
loc = localization
mp = mapping
flp = foodLogicPlan
# Sometimes the logic module uses pretty deep recursion on long expressions
sys.setrecursionlimit(100000)

#______________________________________________________________________________
# Important expression generating functions, useful to read for understanding of this project.


def sensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (
                PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time = t)
        all_percept_exprs.append(percept_unit_clause % disjoin(percept_exprs))

    return conjoin(all_percept_exprs + combo_var_def_exprs)


def fourBitPerceptRules(t: int, percepts: List) -> Expr:
    """
    Localization and Mapping both use the 4 bit sensor, which tells us True/False whether
    a wall is to pacman's north, south, east, and west.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 4, "Percepts must be a length 4 list."

    percept_unit_clauses = []
    for wall_present, direction in zip(percepts, DIRECTIONS):
        percept_unit_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        if not wall_present:
            percept_unit_clause = ~PropSymbolExpr(blocked_str_map[direction], time=t)
        percept_unit_clauses.append(percept_unit_clause) # The actual sensor readings
    return conjoin(percept_unit_clauses)


def numAdjWallsPerceptRules(t: int, percepts: List) -> Expr:
    """
    SLAM uses a weaker numAdjWallsPerceptRules sensor, which tells us how many walls pacman is adjacent to
    in its four directions.
        000 = 0 adj walls.
        100 = 1 adj wall.
        110 = 2 adj walls.
        111 = 3 adj walls.
    """
    assert isinstance(percepts, list), "Percepts must be a list."
    assert len(percepts) == 3, "Percepts must be a length 3 list."

    percept_unit_clauses = []
    for i, percept in enumerate(percepts):
        n = i + 1
        percept_literal_n = PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t)
        if not percept:
            percept_literal_n = ~percept_literal_n
        percept_unit_clauses.append(percept_literal_n)
    return conjoin(percept_unit_clauses)


def SLAMSensorAxioms(t: int, non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    all_percept_exprs = []
    combo_var_def_exprs = []
    for direction in DIRECTIONS:
        percept_exprs = []
        dx, dy = DIR_TO_DXDY_MAP[direction]
        for x, y in non_outer_wall_coords:
            combo_var = PropSymbolExpr(pacman_wall_str, x, y, x + dx, y + dy, time=t)
            percept_exprs.append(combo_var)
            combo_var_def_exprs.append(combo_var % (PropSymbolExpr(pacman_str, x, y, time=t) & PropSymbolExpr(wall_str, x + dx, y + dy)))

        blocked_dir_clause = PropSymbolExpr(blocked_str_map[direction], time=t)
        all_percept_exprs.append(blocked_dir_clause % disjoin(percept_exprs))

    percept_to_blocked_sent = []
    for n in range(1, 4):
        wall_combos_size_n = itertools.combinations(blocked_str_map.values(), n)
        n_walls_blocked_sent = disjoin([
            conjoin([PropSymbolExpr(blocked_str, time=t) for blocked_str in wall_combo])
            for wall_combo in wall_combos_size_n])
        # n_walls_blocked_sent is of form: (N & S) | (N & E) | ...
        percept_to_blocked_sent.append(
            PropSymbolExpr(geq_num_adj_wall_str_map[n], time=t) % n_walls_blocked_sent)

    return conjoin(all_percept_exprs + combo_var_def_exprs + percept_to_blocked_sent)


def allLegalSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = pacmanSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)


def SLAMSuccessorAxioms(t: int, walls_grid: List[List], non_outer_wall_coords: List[Tuple[int, int]]) -> Expr:
    """walls_grid can be a 2D array of ints or bools."""
    all_xy_succ_axioms = []
    for x, y in non_outer_wall_coords:
        xy_succ_axiom = SLAMSuccessorAxiomSingle(
            x, y, t, walls_grid)
        if xy_succ_axiom:
            all_xy_succ_axioms.append(xy_succ_axiom)
    return conjoin(all_xy_succ_axioms)

#______________________________________________________________________________
# Various useful functions, are not needed for completing the project but may be useful for debugging


def modelToString(model: Dict[Expr, bool]) -> str:
    """Converts the model to a string for printing purposes. The keys of a model are 
    sorted before converting the model to a string.
    
    model: Either a boolean False or a dictionary of Expr symbols (keys) 
    and a corresponding assignment of True or False (values). This model is the output of 
    a call to pycoSAT.
    """
    if model == False:
        return "False" 
    else:
        # Dictionary
        modelList = sorted(model.items(), key=lambda item: str(item[0]))
        return str(modelList)


def extractActionSequence(model: Dict[Expr, bool], actions: List) -> List:
    """
    Convert a model in to an ordered list of actions.
    model: Propositional logic model stored as a dictionary with keys being
    the symbol strings and values being Boolean: True or False
    Example:
    >>> model = {"North[2]":True, "P[3,4,0]":True, "P[3,3,0]":False, "West[0]":True, "GhostScary":True, "West[2]":False, "South[1]":True, "East[0]":False}
    >>> actions = ['North', 'South', 'East', 'West']
    >>> plan = extractActionSequence(model, actions)
    >>> print(plan)
    ['West', 'South', 'North']
    """
    plan = [None for _ in range(len(model))]
    for sym, val in model.items():
        parsed = parseExpr(sym)
        if type(parsed) == tuple and parsed[0] in actions and val:
            action, _, time = parsed
            plan[time] = action
    #return list(filter(lambda x: x is not None, plan))
    return [x for x in plan if x is not None]


# Helpful Debug Method
def visualizeCoords(coords_list, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    for (x, y) in itertools.product(range(problem.getWidth()+2), range(problem.getHeight()+2)):
        if (x, y) in coords_list:
            wallGrid.data[x][y] = True
    print(wallGrid)


# Helpful Debug Method
def visualizeBoolArray(bool_arr, problem) -> None:
    wallGrid = game.Grid(problem.walls.width, problem.walls.height, initialValue=False)
    wallGrid.data = copy.deepcopy(bool_arr)
    print(wallGrid)

class PlanningProblem:
    """
    This class outlines the structure of a planning problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the planning problem.
        """
        util.raiseNotDefined()

    def getGhostStartStates(self):
        """
        Returns a list containing the start state for each ghost.
        Only used in problems that use ghosts (FoodGhostPlanningProblem)
        """
        util.raiseNotDefined()
        
    def getGoalState(self):
        """
        Returns goal state for problem. Note only defined for problems that have
        a unique goal state such as PositionPlanningProblem
        """
        util.raiseNotDefined()