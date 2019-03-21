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
	day: Int,
	left: World -> set Prisoner
} { 
	this = KS/first implies day = 1
}

-- can see all other prisoners other than themselves
fun visibleTo[p: Prisoner] : set Prisoner {
	Prisoner - p
}

fun canLeave[ks: KnowledgeState, w: World] : set Prisoner {
	{p: Prisoner | ks.poss[p][w] = {w}}
}

pred initialKnowledge[ks: KnowledgeState] {
	-- each prisoner can see all the other prisoners
	-- and they are unable to see themselves
	
	all p: Prisoner | all w: World {
		-- reads as, for each prisoner visible to the current prisoner,
		-- all possible worlds for the current prisoner will have the 
		-- other prisoner with the same eyecolor  
		ks.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p']
			and some ow.eyes.Blue
		}
		all w: World {
			ks.left[w] = canLeave[ks, w]
		}
	}
}

pred transition[ks, ks': KnowledgeState] {
	ks'.day = add[ks.day, 1]
	all p: Prisoner | all w: World { 
		ks'.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p'] 
			and canLeave[ks, ow] = canLeave[ks, w]
			and ow in ks.poss[p][w]
		}
	}
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

run{} for exactly 1 Prisoner,  exactly 2 World, exactly 7 KnowledgeState

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
n days each of them will have left
*/
check blueEyesLeave {
	all w: World | all ks: KnowledgeState | {
		someBlueEyes[w] implies {
			ks.day = #w.eyes.Blue implies ks.left[w] = w.eyes.Blue
		}
	}
} for exactly 2 Prisoner,  exactly 4 World, exactly 4 KnowledgeState

