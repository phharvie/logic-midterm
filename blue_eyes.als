open util/ordering[KnowledgeState] as KS

abstract sig EyeColor {}

-- Eyes are either blue or green
one sig Blue extends EyeColor{}
one sig Green extends EyeColor{}

sig Prisoner {}

-- The world maps prisoners to eye colors
sig World {
	eyes: Prisoner -> one EyeColor,
	left: set Prisoner
}

-- no two worlds are the same
fact distWorlds {
	all disj w1, w2: World | 
		some p: Prisoner | w1.eyes[p] != w2.eyes[p]
}

fact someBlueEyes {
	all w: World | {
		some p: Prisoner | w.eyes[p] = Blue
	}
}

sig KnowledgeState {
	-- poss[p][w1][w2] read as: 
		-- If p is in w1, they believe w2 is possible
	poss: Prisoner->World->World,
	night: Int
} { 
	this = KS/first implies night = 0
	this != KS/first implies night > 0
}

-- can see all other prisoners other than themselves
fun visibleTo[p: Prisoner] : set Prisoner {
	Prisoner - p
}

fun visibleBlueEyes[w: World, p: Prisoner] : set Prisoner {
	w.eyes.Blue - p
}

pred canLeave[ks: KnowledgeState, p: Prisoner, w: World] {
	one ks.poss[p][w] and w.eyes[p] = Blue
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
		}
	}
}

fun changeWorld[ks: KnowledgeState, p: Prisoner, w: World] : set Prisoner {
	canLeave[ks, p, w] implies w.left + p else w.left
}
	

pred transition[ks: KnowledgeState, ks': KnowledgeState] {
	all p: Prisoner | all w: World { 
		ks'.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p'] and 
			(ow = w or #ks.poss[p'][ow] > 1)
		}
	}
}

pred consistent[ks: KnowledgeState] {
	all p: Prisoner | all w: World {
		w in ks.poss[p][w]
	}
}

pred onIsland[ks: KnowledgeState] {
	all w: World {
		w.left = none
	}
}

fact initialState {
	consistent[KS/first]
	initialKnowledge[KS/first]
	onIsland[KS/first]
}

fact nextState {
	consistent[KS/first.next]
	transition[KS/first, KS/first.next]
}

run{} for exactly 2 Prisoner,  exactly 3 World,
exactly 3 KnowledgeState
