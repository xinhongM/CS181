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

class ReflexAgent(Agent):
    """
    A reflex agent chooses an action at each choice point by examining
    its alternatives via a state evaluation function.

    The code below is provided as a guide.  You are welcome to change
    it in any way you see fit, so long as you don't touch our method
    headers.
    """


    def getAction(self, gameState):
        """
        You do not need to change this method, but you're welcome to.

        getAction chooses among the best options according to the evaluation function.

        Just like in the previous project, getAction takes a GameState and returns
        some Directions.X for some X in the set {NORTH, SOUTH, WEST, EAST, STOP}
        """
        # Collect legal moves and child states
        legalMoves = gameState.getLegalActions()

        # Choose one of the best actions
        scores = [self.evaluationFunction(gameState, action) for action in legalMoves]
        bestScore = max(scores)
        bestIndices = [index for index in range(len(scores)) if scores[index] == bestScore]
        chosenIndex = random.choice(bestIndices) # Pick randomly among the best

        "Add more of your code here if you want to"

        return legalMoves[chosenIndex]

    def evaluationFunction(self, currentGameState, action):
        """
        Design a better evaluation function here.

        The evaluation function takes in the current and proposed child
        GameStates (pacman.py) and returns a number, where higher numbers are better.

        The code below extracts some useful information from the state, like the
        remaining food (Foods) and Pacman position after moving (newPos).
        ScaredTimes holds the number of moves that each ghost will remain
        scared because of Pacman having eaten a power pellet.

        Print out these variables to see what you're getting, then combine them
        to create a masterful evaluation function.
        """
        # Useful information you can extract from a GameState (pacman.py)
        childGameState = currentGameState.getPacmanNextState(action)
        newPos = childGameState.getPacmanPosition()
        Foods = childGameState.getFood()
        GhostStates = childGameState.getGhostStates()
        ScaredTimes = [ghostState.scaredTimer for ghostState in GhostStates]

        "*** YOUR CODE HERE ***"
        foodsPos = Foods.asList()
        foodsCount = len(foodsPos)
        closest = 9999 # initial very large

        for i in range(0, foodsCount):
          distance = manhattanDistance(foodsPos[i], newPos) + foodsCount * 100
          closest = min(closest, distance)
        score = -closest

        if foodsCount == 0 :
          return 0

        for i in range(0, len(GhostStates)):
          ghostPos = childGameState.getGhostPosition(i+1)
          if manhattanDistance(newPos,ghostPos) <= 1 : # touch the ghost
            score = -9999

        return score

        

def scoreEvaluationFunction(currentGameState):
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

    def getAction(self, gameState):
        """
        Returns the minimax action from the current gameState using self.depth
        and self.evaluationFunction.

        Here are some method calls that might be useful when implementing minimax.

        gameState.getLegalActions(agentIndex):
        Returns a list of legal actions for an agent
        agentIndex=0 means Pacman, ghosts are >= 1

        gameState.getNextState(agentIndex, action):
        Returns the child game state after an agent takes an action

        gameState.getNumAgents():
        Returns the total number of agents in the game

        gameState.isWin():
        Returns whether or not the game state is a winning state

        gameState.isLose():
        Returns whether or not the game state is a losing state
        """
        "*** YOUR CODE HERE ***"
        
        def Maximizer(gameState, dep): #For pacman
          currentDepth = dep + 1
          maxValue = -99999
          if gameState.isWin() or gameState.isLose() or currentDepth == self.depth:
            return self.evaluationFunction(gameState)
          else:
            for action in gameState.getLegalActions(0): # index = 0 for pacman
              nextState = gameState.getNextState(0, action)
              maxValue = max (Minimizer(nextState, currentDepth, 1), maxValue,)
          return maxValue

          
        def Minimizer(gameState, dep, ghostindex): #For ghost
          minValue = 99999
          if gameState.isWin() or gameState.isLose() or dep == self.depth:
            return self.evaluationFunction(gameState)
          else:
            for action in gameState.getLegalActions(ghostindex):
              nextState = gameState.getNextState(ghostindex, action)
              if ghostindex < gameState.getNumAgents() - 1:
                minValue = min(minValue, Minimizer(nextState, dep, ghostindex+1))
              else:
                minValue = min(minValue, Maximizer(nextState, dep))
          return minValue
        
        # main 
        currentValue = -99999
        for action in gameState.getLegalActions(0):
          nextState = gameState.getNextState(0, action)
          value = Minimizer(nextState, 0, 1)
          if value >= currentValue:
            result = action
            currentValue = value
        return result

        util.raiseNotDefined()

class AlphaBetaAgent(MultiAgentSearchAgent):
    """
    Your minimax agent with alpha-beta pruning (question 3)
    """

    def getAction(self, gameState):
        """
        Returns the minimax action using self.depth and self.evaluationFunction
        """
        "*** YOUR CODE HERE ***"
        def Maximizer(gameState, dep, alpha, beta):
          currentDepth = dep + 1
          maxValue = -99999
          if gameState.isWin() or gameState.isLose() or currentDepth == self.depth:
            return self.evaluationFunction(gameState)
          else:
            temp_alpha = alpha
            for action in gameState.getLegalActions(0): # index = 0 for pacman
              nextState = gameState.getNextState(0, action)
              maxValue = max (Minimizer(nextState, currentDepth, 1, temp_alpha, beta), maxValue,)
              #
              if maxValue > beta:
                return maxValue
              temp_alpha = max( temp_alpha, maxValue)
          return maxValue
          
        
        #For all ghosts.
        def Minimizer(gameState, dep, ghostindex, alpha, beta): #For ghost
          minValue = 99999
          if gameState.isWin() or gameState.isLose() or dep == self.depth:
            return self.evaluationFunction(gameState)
          else:
            temp_beta = beta
            for action in gameState.getLegalActions(ghostindex):
              nextState = gameState.getNextState(ghostindex, action)
              if ghostindex < gameState.getNumAgents() - 1:
                minValue = min(minValue, Minimizer(nextState, dep, ghostindex+1, alpha, temp_beta))
              else:
                minValue = min(minValue, Maximizer(nextState, dep, alpha, temp_beta))
              #
              if alpha > minValue:
                return minValue  
              temp_beta = min(temp_beta, minValue)
          return minValue
        
        # main 
        currentValue = -99999
        alpha = -99999
        beta = 99999
        for action in gameState.getLegalActions(0):
          nextState = gameState.getNextState(0, action)
          value = Minimizer(nextState, 0, 1, alpha, beta)
          if value >= currentValue:
            result = action
            currentValue = value
          if value > beta:
            return result
          alpha = max(alpha, value)
        return result

        
        
class ExpectimaxAgent(MultiAgentSearchAgent):
    """
      Your expectimax agent (question 4)
    """

    def getAction(self, gameState):
        """
        Returns the expectimax action using self.depth and self.evaluationFunction

        All ghosts should be modeled as choosing uniformly at random from their
        legal moves.
        """
        "*** YOUR CODE HERE ***"
        def Maximizer(gameState, dep): #For pacman
          currentDepth = dep + 1
          maxValue = -99999
          if gameState.isWin() or gameState.isLose() or currentDepth == self.depth:
            return self.evaluationFunction(gameState)
          else:
            for action in gameState.getLegalActions(0): # index = 0 for pacman
              nextState = gameState.getNextState(0, action)
              maxValue = max (Expecti(nextState, currentDepth, 1), maxValue,)
          return maxValue

        def Expecti(gameState, dep, ghostindex):
          ex_value = 0
          if gameState.isWin() or gameState.isLose() or dep == self.depth:
            return self.evaluationFunction(gameState)
          else:
            action_mun = len(gameState.getLegalActions(ghostindex))
            if action_mun == 0:
              return 0
            for action in gameState.getLegalActions(ghostindex):
              nextState = gameState.getNextState(ghostindex, action)
              if ghostindex < gameState.getNumAgents() - 1:
                ex_value += Expecti(nextState, dep, ghostindex+1)/action_mun
              else:
                ex_value += Maximizer(nextState, dep)/action_mun
          return ex_value

        currentValue = -99999
        for action in gameState.getLegalActions(0):
          nextState = gameState.getNextState(0, action)
          value = Expecti(nextState, 0, 1)
          if value >= currentValue:
            result = action
            currentValue = value
        return result

        util.raiseNotDefined()

def betterEvaluationFunction(currentGameState):
    """
    Your extreme ghost-hunting, pellet-nabbing, food-gobbling, unstoppable
    evaluation function (question 5).

    DESCRIPTION: <write something here so we know what you did>
    """
    "*** YOUR CODE HERE ***"
    Pos = currentGameState.getPacmanPosition()
    Foods = currentGameState.getFood()
    GhostStates = currentGameState.getGhostStates()
    ScaredTimes = [ghostState.scaredTimer for ghostState in GhostStates]
    
    # distance to the foods 
    foodList = Foods.asList()
    foodDistance = [util.manhattanDistance(Pos,positon) for positon in foodList]

    # distance to each ghost 
    ghostPos = [ghost.getPosition() for ghost in GhostStates]    
    ghostDistance = [util.manhattanDistance(Pos,positon) for positon in ghostPos]

    # we add something "good" and subtraction the "bad"
    score = currentGameState.getScore() + sum(ScaredTimes) - sum(foodDistance) + len(Foods.asList(False)) - len(currentGameState.getCapsules()) - sum (ghostDistance)
       
    return score
    util.raiseNotDefined()

# Abbreviation
better = betterEvaluationFunction

class ContestAgent(MultiAgentSearchAgent):
    """
      Your agent for the mini-contest
    """

    def getAction(self, gameState):
        """
          Returns an action.  You can use any method you want and search to any depth you want.
          Just remember that the mini-contest is timed, so you have to trade off speed and computation.

          Ghosts don't behave randomly anymore, but they aren't perfect either -- they'll usually
          just make a beeline straight towards Pacman (or away from him if they're scared!)
        """
        "*** YOUR CODE HERE ***"
            
        util.raiseNotDefined()