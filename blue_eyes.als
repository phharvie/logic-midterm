-- impose ordering on knowledge states to model
-- cumlative knowledge over time of prisoners
open util/ordering[KnowledgeState] as KS

abstract sig EyeColor {}
-- Eyes are either blue or green
one sig Blue extends EyeColor{}
one sig Green extends EyeColor{}

sig Prisoner {}

-- The world maps prisoners to eye colors
sig World {
	eyes: Prisoner -> one EyeColor
}

-- no two worlds are the same
fact distWorlds {
	all disj w1, w2: World | 
		some p: Prisoner | w1.eyes[p] != w2.eyes[p]
}

sig KnowledgeState {
	-- poss[p][w1][w2] read as: 
		-- If p is in w1, they believe w2 is possible
	poss: Prisoner->World->World,
	-- the number of days passed on the island
	day: Int,
	-- a mapping from worlds to the set of prisoners that have
	-- left them
	left: World -> set Prisoner
} { 
	-- at the initial knowledge state, the day number is 1
	this = KS/first implies day = 1
}

-- prisoners can see all other prisoners other than themselves
fun visibleTo[p: Prisoner] : set Prisoner {
	Prisoner - p
}

-- given a knowledge state and a world, the set of prisoners that 
-- can leave from that world are the ones that only beleive in the
-- world they are in
fun canLeave[ks: KnowledgeState, w: World] : set Prisoner {
	{p: Prisoner | ks.poss[p][w] = {w}}
}

-- the initialKnowledge predicate (defined below) must hold for the
-- first knowledge state
fact initialState {
	initialKnowledge[KS/first]
}

pred initialKnowledge[ks: KnowledgeState] {
	-- given the first KS, for all the prisoners and all the worlds
	all p: Prisoner | all w: World {
		-- reads as, for each prisoner p' visible to the current prisoner p,
		-- the set of possible worlds for p given that it is in w is the set of
		-- all worlds in which p' eye colors stay the same
		ks.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p']
			and some ow.eyes.Blue
		}
		-- the set of people who have left that world then contains
		-- the prisoners that can leave at that day
		all w: World {
			ks.left[w] = canLeave[ks, w]
		}
	}
}

-- for each knowledge state apart from the last one, there must be
-- a transition (defined below) between the current and next knowledge states
fact traces {
	all ks: KnowledgeState - KS/last | {
		transition[ks, ks.next]
	}
}

-- defines what a transition between a current state ks and its 
-- consequent state ks' is
pred transition[ks, ks': KnowledgeState] {
	-- the number of days passed in the next state ks' is 1 greater
	-- than the number of days passed in the current state
	ks'.day = add[ks.day, 1]
	
	-- given the first KS, for all the prisoners and all the worlds
	all p: Prisoner | all w: World { 
		-- reads as, the set of worlds that prisoner p thinks are
		-- possible in the next knowledge state ks' given that it is
		-- in w is the set of worlds which satisfy the following conditions:
		--   (1) the eye colors of prisoners p' visible to p are 
		--       the same to the eye colors they had in w
		--   (2) prisoners who could leave from world w
		--       should still be able to leave in these worlds
		--   (3) these worlds must be in the set of worlds that p thinks
		--       are possible given the previous knowledge state
		ks'.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p'] 
			and canLeave[ks, ow] = canLeave[ks, w]
			and ow in ks.poss[p][w]
		}
	}
	-- the set of people who have left that world in the next knowledge
	-- state then contains the prisoners that can leave at that day
	all w: World {
		ks'.left[w] = canLeave[ks', w]
	}
}

run{} for exactly 3 Prisoner,  exactly 8 World, exactly 7 KnowledgeState

-- a knowledge state is consistent if all prisoners p in
-- their worlds w beleieve that the world they are currently 
-- in is possible
pred consistent[ks: KnowledgeState] {
	all p: Prisoner, w: World | {
		w in ks.poss[p][w]
	}
}
--------------- sanity checks --------------- 

check allConsistent {
	all ks: KnowledgeState, p: Prisoner, w: World | {
		w in ks.poss[p][w]
	}
}

check everyoneIsAwareEventually {
	all w: World, p: Prisoner | {
		some ks: KnowledgeState | {
			w in ks.poss[p][w]
		}
	}
} for exactly 3 Prisoner,  exactly 8 World, exactly 4 KnowledgeState

