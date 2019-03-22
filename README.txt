______ _              _____                
| ___ \ |            |  ___|               
| |_/ / |_   _  ___  | |__ _   _  ___  ___ 
| ___ \ | | | |/ _ \ |  __| | | |/ _ \/ __|
| |_/ / | |_| |  __/ | |__| |_| |  __/\__ \
\____/|_|\__,_|\___| \____/\__, |\___||___/
                            __/ |          
                           |___/           


Design Choices:
===============

(a) We decided to allow for the existence of a world in which
    no blue-eyes prisoners exist. Prisoners in such a world will
    never leave the island because they will always think there is
    a blue-eyed person (given what the Guru says) although there 
    isn't. We accounted for this edge case in our transition predicate.

(b) We decided to allow for only 2 eye colors on the island. The xkcd
    puzzle linked-to in the assignment states that there are only two
    colors so we followed that convention. However, having multiple other
    colors should not be a lot more different than having only 2 colors
    since we can treat the colors as Blue and Not Blue.

(c) We added a 'left' relation to our knowledge state signature which
    maps worlds to the set of prisoners that have left them. This was 
    extremely useful for us to debug in Alloy's table view, and is also
    used to show the set of prisoners who have left each world by every
    knowledge state (at every day).

(d) We added a few sanity checks/tests to check the functionality of our
    model. These included a test to check that all worlds in all knowledge
    states are consistent, a test to check that everyone is aware of their
    eye color eventually, a test to check that in a world that is not entirely
    composed of green-eyed prisoners all prisoners become aware of their eye color
    at once, a test to check that n blue-eyed prisoners in a given world all leave
    after n + 1 days, and finally, a test to check that the 'left' set is maintained
    after everyone has left.



Model Structure:
================

Our modeled is built around 3 main signatures:

(a) Prisoners, who are the inhabitants of the island; each with blue or 
    green eyes.

(b) Worlds, disjoint, and containing a mapping from each prisoner in them
    to their corresponding eye color.

(c) Knowledge States, which represent our current knowledge about the world.
    It contains an integer, representing the number of days passed on the island,
    a mapping from prisoners and their current worlds to worlds they believe are
    possible, and another mapping from worlds to the set of prisoners that have left
    them. Knowledge states are ordered via the util/ordering library to represent
    knowledge progression with time.

We solved this problem through two segments of operations on knowledge state attributes.

I.  The first operation involved defining the initial knowledge state we have at the
    beginning of the problem; we define the set of possible worlds of each prisoner
    given their current world as the set of worlds in which eye colors visible to this
    prisoner stay the same. We also define the set of prisoners that left each world
    via a function (canLeave) that takes in a knowledge state and a world and returns 
    the set of prisoners who believe that the only possible world is the world they are
    in.

II. The second operation involved defining the transition (progression) of knowledge
    over intermediate states; we define the set of possible worlds of each prisoner
    in the next state given their current world in the next as a subset of worlds they
    believed in the previous state in which eye colors visible to this prisoner stay the
    same, and the set of people who left that world stays the same. We also define the set
    of prisoners that left each world in the next state via a function (canLeave) that 
    takes in a knowledge state and a world and returns the set of prisoners who believe
    that the only possible world is the world they are in. Finally, we increment the day
    count by one to account for the fact that another day has passed on the island.

The structure of our model is outlined in further detail through the in-line
comments we have provided within our code. 



What the model proves:
======================

(a) If there are n prisoners with blue eyes, each blue-eyed prisoner will leave on the nth 
    day.

(b) If there are n prisoners with blue eyes, each prisoner without blue eyes will leave on 
    the nth + 1 day.

(c) If all prisoners do not have blue eyes, then no prisoners will ever leave the island

(d) In a world that is not entirely composed of green-eyed prisoners, all prisoners become  
    aware of their eye color at once.

BUGS:
=====
It takes a while to run the program on 4 prisoners, 16 worlds, possibly due to the left 
relation on knowledge states. A better design would have been to have worlds contain the
set of prisoners that have left them, however, we could not figure out how to get this to
work with alloy (cause its a really confusing language)
