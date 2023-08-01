# search.py
# ---------
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
In search.py, you will implement generic search algorithms which are called by
Pacman agents (in searchAgents.py).
"""

import util

class SearchProblem:
    """
    This class outlines the structure of a search problem, but doesn't implement
    any of the methods (in object-oriented terminology: an abstract class).

    You do not need to change anything in this class, ever.
    """

    def getStartState(self):
        """
        Returns the start state for the search problem.
        """
        util.raiseNotDefined()

    def isGoalState(self, state):
        """
          state: Search state

        Returns True if and only if the state is a valid goal state.
        """
        util.raiseNotDefined()

    def getSuccessors(self, state):
        """
          state: Search state

        For a given state, this should return a list of triples, (successor,
        action, stepCost), where 'successor' is a successor to the current
        state, 'action' is the action required to get there, and 'stepCost' is
        the incremental cost of expanding to that successor.
        """
        util.raiseNotDefined()

    def getCostOfActions(self, actions):
        """
         actions: A list of actions to take

        This method returns the total cost of a particular sequence of actions.
        The sequence must be composed of legal moves.
        """
        util.raiseNotDefined()


def tinyMazeSearch(problem):
    """
    Returns a sequence of moves that solves tinyMaze.  For any other maze, the
    sequence of moves will be incorrect, so only use this for tinyMaze.
    """
    from game import Directions
    s = Directions.SOUTH
    w = Directions.WEST
    return  [s, s, w, s, w, w, s, w]

def depthFirstSearch(problem: SearchProblem):
    """
    Search the deepest nodes in the search tree first.

    Your search algorithm needs to return a list of actions that reaches the
    goal. Make sure to implement a graph search algorithm.

    To get started, you might want to try some of these simple commands to
    understand the search problem that is being passed in:

    print("Start:", problem.getStartState())
    print("Is the start a goal?", problem.isGoalState(problem.getStartState()))
    print("Start's successors:", problem.getSuccessors(problem.getStartState()))
    """
    "*** YOUR CODE HERE ***"

    frontier = util.Stack()
    visited = set()

    # we start from the given state, and we haven't made any steps yet hence the empty list
    node = (problem.getStartState(), [])

    # if the goal state was reached, return no steps 
    if problem.isGoalState(node[0]):
        return []
    
    frontier.push(node)

    while True:
        if frontier.isEmpty():
            return []
        
        # get new node from frontier
        node = frontier.pop()

        # add him to the visited set
        visited.add(node[0])

        # if we reached the goal state on the node
        # return its path up to that point
        if problem.isGoalState(node[0]):
            return node[1]

        nextNodes = problem.getSuccessors(node[0])

        # for successor states, check accordingly
        for ss in nextNodes:
            if ss[0] not in visited:
                # create new path
                # by adding the new action to the actions already in place
                path = node[1] + [ss[1]]
                frontier.push((ss[0], path))
    
    util.raiseNotDefined()

def breadthFirstSearch(problem: SearchProblem):
    """Search the shallowest nodes in the search tree first."""
    "*** YOUR CODE HERE ***"
    
    frontier = util.Queue()
    visited = set()

    # we start from the given state, and we haven't made any steps yet hence the empty list
    node = (problem.getStartState(), [])

    # if the goal state was reached, return no steps 
    if problem.isGoalState(node[0]):
        return []
    
    frontier.push(node)

    while True:
        if frontier.isEmpty():
            return False
        
        # get new node from frontier
        node = frontier.pop()

        # add him to the visited set
        visited.add(node[0])

        # # if we reached the goal state on the node
        # # return its path up to that point
        if problem.isGoalState(node[0]):
            return node[1]

        nextNodes = problem.getSuccessors(node[0])

        # for successor states, check accordingly
        for ss in nextNodes:
            if ss[0] not in visited and ss[0] not in ( states[0] for states in frontier.list):
                # create new path
                # by adding the new action to the actions already in place
                path = node[1] + [ss[1]]
                frontier.push((ss[0], path))
    
    util.raiseNotDefined()

def uniformCostSearch(problem: SearchProblem):
    """Search the node of least total cost first."""
    "*** YOUR CODE HERE ***"

    frontier = util.PriorityQueue()
    visited = set()

    state = problem.getStartState()

    # We signify the starting state by having no parent, no cost and no action prior to that 
    node = {"state" : state, 
            "parent" :None, 
            "cost" : 0,
            "action" : None }

    # FROM THE PQ definition: def push(self, item, priority):
    # So the item -> node, and its priority -> cost to get to that node
    frontier.push(node, node.get("cost"))

    while not frontier.isEmpty():
        node = frontier.pop()
        state = node.get('state')
        cost = node.get('cost')

        if state in visited:
            continue
        elif problem.isGoalState(state) == True:
            break

        visited.add(state)

        for ss in problem.getSuccessors(state):
            if ss[0] not in visited:
                nextNode = {
                    "state": ss[0],
                    "cost" : ss[2] + cost,
                    "parent": node,
                    "action" : ss[1]
                }
                frontier.push(nextNode, nextNode.get("cost"))

    # actions will be created from end to start
    # node begins at the last position (state) since when the state is reached we break
    # and using its parent we travel up (backwords) the tree

    path = []
    while node.get("parent") != None:
        try:
            path = [node["action"]] + path
            node = node["parent"]
        except:
            print("Some key is not present in the dictionary, cannot continue")
            return []

    return path

    util.raiseNotDefined()

def nullHeuristic(state, problem=None):
    """
    A heuristic function estimates the cost from the current state to the nearest
    goal in the provided SearchProblem.  This heuristic is trivial.
    """
    return 0

def aStarSearch(problem: SearchProblem, heuristic=nullHeuristic):
    """Search the node that has the lowest combined cost and heuristic first."""
    "*** YOUR CODE HERE ***"
    
    frontier = util.PriorityQueue()
    startingState = problem.getStartState()
    visited = set()

    # We signify the starting state by having no parent, no cost and no action prior to that 
    # and for A* we add the heuristic in the way we compute the distance
    node = {
        "state" : startingState,
        "parent" : None,
        "cost" : 0,
        "action" : None,
        "h" : heuristic(startingState, problem)
    }

    # FROM THE PQ definition: def push(self, item, priority):
    # So the item -> node, and its priority -> cost to get to that node
    frontier.push(node, node.get("cost") + node.get("h"))

    while not frontier.isEmpty():
        node = frontier.pop()
        state = node.get("state")
        cost = node.get("cost")
        heur = node.get("h")

        if state in visited:
            continue
        elif problem.isGoalState(state) == True:
            break

        visited.add(state)

        for ss in problem.getSuccessors(state):
            if ss[0] not in visited:
                nextNode = {
                    "parent" : node,
                    "state" : ss[0],
                    "cost" : ss[2] + cost,
                    "action" : ss[1],
                    "h" : heuristic(ss[0], problem)
                }
                frontier.push(nextNode, nextNode.get("cost") + nextNode.get("h"))

    # actions will be created from end to start
    # node begins at the last position (state) since when the state is reached we break
    # and using its parent we travel up (backwords) the tree

    path = []
    while node.get("parent") != None:
        try:
            path = [node["action"]] + path
            node = node["parent"]
        except:
            print("Some key is not present in the dictionary, cannot continue")
            return []

    return path

    util.raiseNotDefined()


# Abbreviations
bfs = breadthFirstSearch
dfs = depthFirstSearch
astar = aStarSearch
ucs = uniformCostSearch
