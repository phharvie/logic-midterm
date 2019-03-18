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
	night: Int
} { 
	this = KS/first implies night = 0
	this != KS/first implies night > 0
}

-- can see all other prisoners other than themselves
fun visibleTo[p: Prisoner] : set Prisoner {
	Prisoner - p
}

pred initialKnowledge[s : KnowledgeState] {
	-- each prisoner can see all the other prisoners
	-- and they are unable to see themselves

	all p: Prisoner | all w: World {
		-- reads as, for each prisoner visible to the current prisoner,
		-- all possible worlds for the current prisoner will have the 
		-- other prisoner with the same eyecolor  
		s.poss[p][w] =  {ow: World | 
			all p': visibleTo[p] | ow.eyes[p'] = w.eyes[p']}
	}
}

fact {
	initialKnowledge[KS/first]
}

run {} for exactly 4 Prisoner,  exactly 16 World, exactly 4 KnowledgeState, 5 int
