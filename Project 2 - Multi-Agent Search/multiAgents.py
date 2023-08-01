# multiAgents.py
# --------------
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


from util import manhattanDistance
from game import Directions
import random, util

from game import Agent
from pacman import GameState

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState: GameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and successor states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState: GameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed successor
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (newFood) and Pacman position after moving (newPos).
        newScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        successorGameState = currentGameState.generatePacmanSuccessor(action)
        newPos = successorGameState.getPacmanPosition()
        newFood = successorGameState.getFood()
        newGhostStates = successorGameState.getGhostStates()
        newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]

        "*** YOUR CODE HERE ***"
        from util import manhattanDistance

        nearest_ghost_dist = []
        for ghostState in newGhostStates:
            nearest_ghost_dist.append(manhattanDistance(ghostState.configuration.pos, newPos)) if ghostState.scaredTimer == 0 else 0

        nearest_food_dist = []
        for foodPos in newFood.asList():
            nearest_food_dist.append(manhattanDistance(foodPos, newPos))

        nearestGhostDistance = min(nearest_ghost_dist) if len(nearest_ghost_dist) != 0 else 0
        nearestFoodDistance = min(nearest_food_dist) if len(nearest_food_dist) != 0 else 0

        # the further away from a ghost the better so   -> distance HIGH => we penalize a little
        #                                               -> distance LOW  => we penalize A LOT
        # the further away from a food the worse so     -> distance HIGH => we penalize A LOT
        #                                               -> distance LOW => we penalize a little 

        # further more ->  we pay more attention to nearest distances to ghosts than to food (point is to avoid the ghosts and not die!)

        # We can also check for eating a ghost, and give it a bigger reward than just eating a food
         
        return ( successorGameState.getScore() + nearestGhostDistance / 10.0 + 6.0 / (nearestFoodDistance + 1.0) )

def scoreEvaluationFunction(currentGameState: GameState):
    """
    This default evaluation function just returns the score of the state.
    The score is the same one displayed in the Pacman GUI.

    This evaluation function is meant for use with adversarial search agents
    (not reflex agents).
    """
    return currentGameState.getScore()

class MultiAgentSearchAgent(Agent):
    """
    This class provides some common elements to all of your
    multi-agent searchers.  Any methods defined here will be available
    to the MinimaxPacmanAgent, AlphaBetaPacmanAgent & ExpectimaxPacmanAgent.

    You *do not* need to make any changes here, but you can if you want to
    add functionality to all your adversarial search agents.  Please do not
    remove anything, however.

    Note: this is an abstract class: one that should not be instantiated.  It's
    only partially specified, and designed to be extended.  Agent (game.py)
    is another abstract class.
    """

    def __init__(self, evalFn = 'scoreEvaluationFunction', depth = '2'):
        self.index = 0 # Pacman is always agent index 0
        self.evaluationFunction = util.lookup(evalFn, globals())
        self.depth = int(depth)

class MinimaxAgent(MultiAgentSearchAgent):
    """
    Your minimax agent (question 2)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action from the current gameState using self.depth
        and self.evaluationFunction.

        Here are some method calls that might be useful when implementing minimax.

        gameState.getLegalActions(agentIndex):
        Returns a list of legal actions for an agent
        agentIndex=0 means Pacman, ghosts are >= 1

        gameState.generateSuccessor(agentIndex, action):
        Returns the successor game state after an agent takes an action

        gameState.getNumAgents():
        Returns the total number of agents in the game

        gameState.isWin():
        Returns whether or not the game state is a winning state

        gameState.isLose():
        Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        # util.raiseNotDefined()

        eval, action = self.minimax(gameState, self.depth, 0)
        return action
    
    def minimax(self, gameState, depth, player):
        if gameState.isWin() or gameState.isLose() or depth == 0:
            return (self.evaluationFunction(gameState), Directions.STOP)
        else:
            if self.isPacman(player):
                # here is what happens for the pacman, we want it to maximize
                return self.maximize(gameState, depth, player)

            else:
                # here is what happens for the ghosts, we want them to minimize
                return self.minimize(gameState, depth, player)
    
    def maximize(self, gameState, depth, player):
        
        maxEvaluation = float('-inf')
        nextAction = Directions.STOP

        # if the agent is the last one, go to the next depth and move to the first player (pacman)
        nextPlayer, nextDepth = self.changePly(gameState, depth, player)


        for action in gameState.getLegalActions(player):
            newState = gameState.generateSuccessor(player, action)
            newEvaluation, next = self.minimax(newState, nextDepth, nextPlayer)

            if newEvaluation > maxEvaluation:
                maxEvaluation = newEvaluation
                nextAction = action

        return (maxEvaluation, nextAction)

    def minimize(self, gameState, depth, player):
        
        minEvaluation = float('inf')
        nextAction = Directions.STOP

        # if the agent is the last one, go to the next depth and move to the first player (pacman)
        nextPlayer, nextDepth = self.changePly(gameState, depth, player)


        for action in gameState.getLegalActions(player):
            newState = gameState.generateSuccessor(player, action)
            newEvaluation, next = self.minimax(newState, nextDepth, nextPlayer)

            if newEvaluation < minEvaluation:
                minEvaluation = newEvaluation
                nextAction = action

        return (minEvaluation, nextAction)

    def isPacman(self, agentIndex):
        return True if agentIndex == 0 else False
    
    def isLastAgent(self, gameState, agentIndex):
        return True if gameState.getNumAgents() -1 == agentIndex else False

    def changePly(self,gameState,depth,player):
        if self.isLastAgent(gameState, player):
            nextPlayer , nextDepth = 0 , depth - 1
        else:
            nextPlayer , nextDepth = player + 1, depth
        
        return (nextPlayer, nextDepth)


class AlphaBetaAgent(MultiAgentSearchAgent):
    """
    Your minimax agent with alpha-beta pruning (question 3)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the minimax action using self.depth and self.evaluationFunction
        """
        "*** YOUR CODE HERE ***"
        eval, action = self.minimax(gameState,self.depth,0, float('-inf'), float('inf') )
        return action

    def minimax(self, gameState, depth, player,alpha, beta):
        if gameState.isWin() or gameState.isLose() or depth == 0:
            return (self.evaluationFunction(gameState), Directions.STOP)
        else:
            if self.isPacman(player):
                # here is what happens for the pacman, we want it to maximize
                return self.maximize(gameState, depth, player, alpha, beta)

            else:
                # here is what happens for the ghosts, we want them to minimize
                return self.minimize(gameState, depth, player, alpha, beta)
    
    def maximize(self, gameState, depth, player, alpha, beta):
        
        maxEvaluation = float('-inf')
        nextAction = Directions.STOP

        # if the agent is the last one, go to the next depth and move to the first player (pacman)
        nextPlayer, nextDepth = self.changePly(gameState, depth, player)


        for action in gameState.getLegalActions(player):
            newState = gameState.generateSuccessor(player, action)
            newEvaluation, next = self.minimax(newState, nextDepth, nextPlayer, alpha, beta)

            if newEvaluation > maxEvaluation:
                maxEvaluation = newEvaluation
                nextAction = action
            # this will have been called by a minimizer
            # and we have a value larger than the one guaranteed
            # so no point in checking for more potential moves, we break by returning
            if newEvaluation > beta:
                return (newEvaluation, next)
            alpha = max(alpha, newEvaluation)

        return (maxEvaluation, nextAction)

    def minimize(self, gameState, depth, player, alpha, beta):
        
        minEvaluation = float('inf')
        nextAction = Directions.STOP

        # if the agent is the last one, go to the next depth and move to the first player (pacman)
        nextPlayer, nextDepth = self.changePly(gameState, depth, player)


        for action in gameState.getLegalActions(player):
            newState = gameState.generateSuccessor(player, action)
            newEvaluation, next = self.minimax(newState, nextDepth, nextPlayer, alpha, beta)

            if newEvaluation < minEvaluation:
                minEvaluation = newEvaluation
                nextAction = action

            # this will have been called by a maximizer
            # and we have a value smaller than the one guaranteed
            # so no point in checking for more potential moves, we break by returning
            if newEvaluation < alpha:
                return (newEvaluation, next)
            beta = min(beta, minEvaluation)
        return (minEvaluation, nextAction)

    def isPacman(self, agentIndex):
        return True if agentIndex == 0 else False
    
    def isLastAgent(self, gameState, agentIndex):
        return True if gameState.getNumAgents() -1 == agentIndex else False

    def changePly(self,gameState,depth,player):
        if self.isLastAgent(gameState, player):
            nextPlayer , nextDepth = 0 , depth - 1
        else:
            nextPlayer , nextDepth = player + 1, depth
        
        return (nextPlayer, nextDepth)

class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 4)
    """

    def getAction(self, gameState: GameState):
        """
        Returns the expectimax action using self.depth and self.evaluationFunction

        All ghosts should be modeled as choosing uniformly at random from their
        legal moves.
        """
        "*** YOUR CODE HERE ***"
        value, action = self.expectimax(gameState, self.depth, 0)
        return action
    
    def expectimax(self, gameState, depth, player):

        if depth == 0 or gameState.isLose() or gameState.isWin():
            score = self.evaluationFunction(gameState)
            return (score, Directions.STOP)
        else:
            # If pacman is playing, we want to maximize 
            if self.isPacman(player):
                return self.maximize(gameState, depth, player)
            else:
            # Else play with the odds!
                return self.expecti(gameState, depth, player)
    
    def maximize(self, gameState, depth, player):
        
        nextPlayer, nextDepth = self.changePly(gameState, depth, player)
        
        evals = []
        # For every legal action, get the next State, place it in the childState to evaluate
        childStates = [ gameState.generateSuccessor(player, action) for action in gameState.getLegalActions(player) ]

        # Then, get every one of the possible successors, and get their respective evaluations ('expected utility'.)
        for state in childStates:
            value, action = self.expectimax(state, nextDepth, nextPlayer)
            evals.append(value)

        # Select the max of those evaluations/utilities
        maxEvaluation = max(evals)
        
        # Search for the specific ones that maximize the evaluation
        indexList = [ i for i in range(len(evals)) if evals[i] == maxEvaluation ]
        
        # And out of those (can be many), randomly select one
        maxIndex = random.choice(indexList)
        nextAction = gameState.getLegalActions(player)[maxIndex]

        return (maxEvaluation, nextAction)

    def expecti(self, gameState, depth, player):
        # For the chance nodes:
        # Average of all available utilities -> Expected utility

        nextPlayer, nextDepth = self.changePly(gameState, depth, player)

        evals = []
        nextAction = Directions.STOP
        childStates = [ gameState.generateSuccessor(player, action) for action in gameState.getLegalActions(player) ]

        for state in childStates:
            value, action = self.expectimax(state, nextDepth, nextPlayer)
            evals.append(value)
                    
        assert (len(evals) != 0)
        average = sum(evals) / float(len(evals))

        return (average, nextAction)

    def isPacman(self, agentIndex):
        return True if agentIndex == 0 else False
    
    def isLastAgent(self, gameState, agentIndex):
        return True if gameState.getNumAgents() -1 == agentIndex else False

    def changePly(self,gameState,depth,player):
        if self.isLastAgent(gameState, player):
            nextPlayer , nextDepth = 0 , depth - 1
        else:
            nextPlayer , nextDepth = player + 1, depth
        
        return (nextPlayer, nextDepth)

def betterEvaluationFunction(currentGameState: GameState):
    """
    Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
    evaluation function (question 5).

    DESCRIPTION: <write something here so we know what you did>
    """
    "*** YOUR CODE HERE ***"
    newFood = currentGameState.getFood()
    newPos = currentGameState.getPacmanPosition()
    newGhostStates = currentGameState.getGhostStates()
    newScaredTimes = [ghostState.scaredTimer for ghostState in newGhostStates]


    "*** YOUR CODE HERE ***"
    
    from util import manhattanDistance
    ateGhost = 0

    nearest_ghost_dist = []
    for ghostState in newGhostStates:
        nearest_ghost_dist.append(manhattanDistance(ghostState.configuration.pos, newPos)) if ghostState.scaredTimer == 0 else 0
    nearest_food_dist = []
    for foodPos in newFood.asList():
        nearest_food_dist.append(manhattanDistance(foodPos, newPos))

    nearestGhostDistance = min(nearest_ghost_dist) if len(nearest_ghost_dist) != 0 else 0
    nearestFoodDistance = min(nearest_food_dist) if len(nearest_food_dist) != 0 else 0
    # the further away from a ghost the better so   -> distance HIGH => we penalize a little
    #                                               -> distance LOW  => we penalize A LOT
    # the further away from a food the worse so     -> distance HIGH => we penalize A LOT
    #                                               -> distance LOW => we penalize a little 
    # further more ->  we pay more attention to nearest distances to ghosts than to food (point is to avoid the ghosts and not die!)
    # so we *multiply* by a factor for the ghost distance, and *divide *for the food distance
    # remembering that we choose the *max* of these scores
    # We can also check for eating a ghost, and give it a bigger reward than just eating a food

    for ghostState in newGhostStates:
        if ghostState.scaredTimer != 0 and ghostState.getPosition() == newPos:
            ateGhost = 400

    return currentGameState.getScore() - 3.0 / (nearestGhostDistance + 1.0) - (nearestFoodDistance / 4.0) + ateGhost

# Abbreviation
better = betterEvaluationFunction
