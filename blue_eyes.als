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
			some ow.eyes.Blue and
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p']
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

fact initialState {
	initialKnowledge[KS/first]
}

fact traces {
	all ks: KnowledgeState - KS/last | {
		transition[ks, ks.next]
	}
}

run{} for exactly 3 Prisoner,  exactly 8 World, exactly 7 KnowledgeState

-- a person with blue eyes exists in that world
pred someBlueEyes[w: World] {
	some p: Prisoner | w.eyes[p] = Blue
}

--------------- sanity checks --------------- 

/* 
checks that consistency is maintained for all worlds that are not composed
of only green eyed people (meaning that the people in that world believe
their world is possible)
*/
check allConsistent {
	all ks: KnowledgeState, w: World, p: Prisoner {
		-- if there exists someone with blue eyes, then everyone in that world
		-- believes that world is possible
		someBlueEyes[w] implies w in ks.poss[p][w]
	}
} for exactly 3 Prisoner, exactly 8 World, exactly 7 KnowledgeState

/*
checks that for everyone world not composed of only green eyed people,
there will a knowledge state where each person is aware of the eye color
*/
check everyoneIsAwareEventually {
	all w: World, p: Prisoner | some ks: KnowledgeState | {
		someBlueEyes[w] implies {
			ks.poss[p][w]  = {w}
		}
	}
} for exactly 3 Prisoner,  exactly 8 World, exactly 4 KnowledgeState


/*
checks that for everyone world not composed of only green eyed people,
there's a knowledge state where every person is aware of their eye color
*/
check everyoneIsAwareAtOnce {
	all w: World | some ks: KnowledgeState | {
		someBlueEyes[w] implies {
			all p: Prisoner | ks.poss[p][w] = {w}
		}
	}
} for exactly 3 Prisoner,  exactly 8 World, exactly 4 KnowledgeState

/*
Check that if there are n blue eyed people in a given world, then after
n days each of them will have left, and before that no one has left
*/
check blueEyesLeaveAfterNdays {
	all w: World | all ks: KnowledgeState | {
		someBlueEyes[w] implies {
			-- if that day is equal to the number of blue eyes in a given world
			ks.day = #w.eyes.Blue implies {
				-- left is equal to all the people with blue eyes
				ks.left[w] = w.eyes.Blue
				-- and no one has left prior
				ks.prev.left[w] = none
			}
		}
	}
} for exactly 3 Prisoner,  exactly 8 World, exactly 4 KnowledgeState

/*
Check that if there are n blue eyed people in a given world, then 
after n + 1 days, everyone will have left, regardless of eye
*/
check everyoneLeavesAfterNplusOneDays {
	all w: World | all ks: KnowledgeState | {
		someBlueEyes[w] implies {
			-- if that day is equal to the number of blue eyes  in a given world plus one
			ks.day = add[#w.eyes.Blue, 1] implies {
				-- left is equal to everyone
				ks.left[w] = w.eyes.EyeColor
				-- and prior state is equal to blue eyes

			}
		}
	}
} for exactly 1 Prisoner,  exactly 2 World, exactly 4 KnowledgeState

/*
Checks that the left status remains the same after everyone has left
*/
check maintainLeftStatus {}
