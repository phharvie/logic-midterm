  /*
  Prisoner Gnomes (TN Spring 2018)
  The gnomes all know who is in each room.
  They do not know the color of their hats,
    or the hats of anyone behind them.
  They are able to see the color of the hats
    of anyone ahead of them.

  Limitation: assume 2 colors, 4 gnomes, 2red/2blue.
*/

open util/ordering[Gnome] as Lineup

-- Disable ordering on KS for debugging as needed
open util/ordering[KnowledgeState] as KS

-- Gnomes are partitioned into 2 separate rooms
-- and, in each room, lined up in (arbitrary) order
-- AN INSTANCE HAS A FIXED ROOM SETUP
sig Gnome {
  room: Room
}
abstract sig Room {}
one sig LeftRoom  extends Room {}
one sig RightRoom extends Room {}

-- Hats are either red or blue
abstract sig HatColor {}
one sig Red  extends HatColor {}
one sig Blue extends HatColor {}

-- A possible world is an allocation of hats
sig World {
  hats: Gnome -> one HatColor
}
-- no two worlds have the same hat allocation
fact canonicalWorlds {
  all disj w1, w2: World |
    some g: Gnome | w1.hats[g] != w2.hats[g]
}
fact halfRedHalfBlue {
  all w: World |
    #{g: Gnome | w.hats[g] = Blue} =
    #{g: Gnome | w.hats[g] = Red}
}

-- Before every question, gnomes have a certain knowledge state
sig KnowledgeState {
  -- Read as: poss[g][w1][w2] means
  --    "If g is in w1, they believe w2 is possible."
  poss: Gnome -> World -> World,
  justAsked: lone Gnome
} {
  this = KS/first implies no justAsked
  this != KS/first implies some justAsked
  -- no repeats (note: still safe even for KS/first)
  no ks: KnowledgeState - this |
    ks.@justAsked = justAsked
}

-- Who can the gnomes see in this instance?
fun visibleTo[g: Gnome]: set Gnome {
	g.^(Lineup/next) & {g': Gnome | g'.room = g.room}
}

pred initialKnowledge[s: KnowledgeState] {
  -- Each gnome can see those later in their ordering
  -- So some gnomes know that /some/ worlds are impossible right away
  all g: Gnome, w: World | {
      s.poss[g][w] =
       {ow: World |
          all g': visibleTo[g] | ow.hats[g'] = w.hats[g'] }
  }
}
fact init {
  -- Easier to debug as separate predicate, because we can
  -- enable or disable the knowledge ordering easily:
  //initialKnowledge[KnowledgeState] -- use for debugging, if only one KS
  initialKnowledge[KS/first] -- use for actual puzzle
}

pred knows[ks: KnowledgeState, g: Gnome, w: World] {
  one ks.poss[g][w] -- exactly ONE world left
  -- Note: this will return true even for an inconsistent state
}
pred learn[old, new: KnowledgeState] {
// if I am visible to justAsked, and doesn't know, maybe I learn something
  all g: Gnome, w: World | {
    -- if new.justAsked is behind me, and doesn't know, then I've learned
    -- that no two distinct gnomes in front of THEM have the same color hat.
    g in visibleTo[new.justAsked] => new.poss[g][w] =
      {ow: World |
        ow in old.poss[g][w] and
        all disj g', g'': visibleTo[new.justAsked] | ow.hats[g'] != ow.hats[g'']}
    else new.poss[g][w] = old.poss[g][w] // didn't learn anything
  }
}

fact traces {
  all ks: KnowledgeState - KS/last | {
    learn[ks, ks.next]
  }
}

-- Every gnome has a hat color, but we know that the colors are
-- evenly distributed. So really choosing position of 2 blues in 4 spots,
-- without repetition: 4c2 = 6. There are 4 gnomes, so a knowledge state
-- exists before each is asked the question.

run {} for 2 HatColor, 4 Gnome, 2 Room,
           exactly 6 World, exactly 1 KnowledgeState, 5 int
run {} for 2 HatColor, 4 Gnome, 2 Room,
           exactly 6 World, exactly 5 KnowledgeState, 5 int
----------------------------
-- Sanity checking on initial state

pred consistent[ks: KnowledgeState] {
  all g: Gnome | all w: World | {
    w in ks.poss[g][w]
  }
}
check firstConsistent {consistent[KS/first]}
  for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int

-- Expect this one to fail
check allConsistent {all ks: KnowledgeState | consistent[ks]}
  for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int
----------------------------
-- SOLUTION CHECKING
----------------------------
-- All of these must assume proper gnome positioning (1, 3)

-- In worlds where the last 2 gnomes are in same room + same color hats
--  Someone can answer in initial state
-- Succeeds
check someoneSolvesInitially {
  {
    #room.LeftRoom = 1
    #room.RightRoom = 3
    last.room = last.prev.room
  } implies some winner: Gnome | { -- same gnome, regardless of hat positioning
    all w: World | w.hats[last] = w.hats[last.prev] implies
      first.poss[winner][w] = w
  }
} for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int

-- Fails! No guarantee on justAsked ordering
check someoneSolvesEventually {
  {
    #room.LeftRoom = 1
    #room.RightRoom = 3
  } implies some ks: KnowledgeState, winner: Gnome | {
    all w: World | ks.poss[winner][w] = w
  }
} for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int



-- Asking order is identical to lineup order
pred niceAskingOrder {
  KS/first.next.justAsked = Lineup/first
  all ks: KnowledgeState-(KS/first+KS/first.next) | {
    ks.justAsked = (ks.KS/prev).justAsked.Lineup/next
  }
}

-- Not yet enough!
check someoneSolvesEventually_restrictJustAsked {
  {
    #room.LeftRoom = 1
    #room.RightRoom = 3
    niceAskingOrder
  } implies some ks: KnowledgeState, winner: Gnome | {
    all w: World | ks.poss[winner][w] = w
  }
} for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int

-- one possible world: too strong!
-- instead: all poss worlds have same hat color for winner
check someoneSolvesEventually_restrictJustAsked_multiworld {
  {
    #room.LeftRoom = 1
    #room.RightRoom = 3
    niceAskingOrder
  } implies some ks: KnowledgeState, winner: Gnome | {
    all w: World | w in ks.poss[winner][w] implies -- every still-consistent world
      all w': ks.poss[winner][w] |                 -- has same hat color as
        w'.hats[winner] = w.hats[winner]           -- its possible worlds
  }
} for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int

-- Make sure that 2nd implies doesn't have unsat antecedent
run sanityCheck2ndLayer {
  #room.LeftRoom = 1
  #room.RightRoom = 3
  niceAskingOrder
  some ks: KnowledgeState, winner: Gnome, w: World |
    w in ks.poss[winner][w]
} for 2 HatColor, 4 Gnome, 2 Room,
  exactly 6 World, exactly 5 KnowledgeState, 5 int

-- Wait: isn't it possible for 0|123? Then 2 can't learn in time...
-- Ahh, but the property about eventual knowledge still holds,
--   it's just that poor gnome 2 can't use their knowledge.
