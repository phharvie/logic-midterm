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

	whoLeft: World -> Int -> set Prisoner
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
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p'] and some ow.eyes.Blue
		}
	}
}

pred transition[ks, ks': KnowledgeState] {
	ks'.day = add[ks.day, 1]
	all w: World {
		ks'.whoLeft[w][ks.day] = canLeave[ks, w] - canLeave[ks.prev, w]
	}
	all p: Prisoner | all w: World { 
		ks'.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p'] 
			and canLeave[ks, ow] = canLeave[ks, w]
			and some ow.eyes.Blue
		}
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

run{} for exactly 2 Prisoner,  exactly 4 World, exactly 7 KnowledgeState

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

