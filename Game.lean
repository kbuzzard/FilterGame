import Game.Levels.SetWorld

-- Here's what we'll put on the title screen
Title "The Filter Game"
Introduction
"
# Welcome to the Filter Game

## What is this game?

There's a mathematical object called a *filter*. It doesn't get much love.
It's not often taught in an undergraduate degree. Furthermore, there are
bad ways to teach it, which can end up with you being more confused than
when you started. Indeed, the author of this game was confused about filters
for many years.

This game is an attempt to explain filters in an intuitive way, as
\"generalised sets\". If you have been brainwashed by the textbook
approach to mathematics, you'll know that infinity is not a number,
that `dy/dx` doesn't mean `dy` divided by `dx` because `dx` isn't
a number, and that `0.999999999999999... = 1` because the difference
between them is infinitely small, and there are no infinitely small
numbers apart from `0`. Well, filters let you recover these intuitive
ideas in a rigorous way which doesn't lead to contradictions.

## What are the prerequisites for playing?

First, there are some mathematical prerequisites. You will need to know
about the abstract concepts of sets and subsets, and functions between sets.
You don't need much more than that. You can learn about these ideas
in any first course or textbook on abstract mathematics, for example
Martin Liebeck's book \"A Concise Introduction to Pure Mathematics\".

And then there are some Lean prerequisites. Lean is an interactive
theorem prover, and this game is written in Lean; you can see
the source code to the game [here](https://github.com/kbuzzard/FilterGame)
on GitHub, and even clone it yourself and add your own levels if you want.
In this game I will assume you know the following basic Lean tactics:
**TODO** fill these in. If you don't know these tactics, then you could
try playing a few worlds in the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).
If you've platyed through Tutorial World, Addition World and Implication World in that
game, then you know enough about Lean to play the Filter Game.

## Getting started

If you satisfy the prerequisites, get started by clicking on `Set World`!
"

Info "
Version 0.1.0: experimental prerelease.

## History

The Filter Game has been a long time coming. I (Kevin Buzzard)
started experimenting with it in about 2020. The first Lean 4 project
I ever embarked on in 2021 was some Filter Game levels (I had to define
a filter in Lean 4 as part of it!). I then supervised a second
year group project on filters in 2023, and Billy Miao put together
a preliminary version (in Lean 3) as part of the project. I thank
Billy and the other group members **TODO** for their thoughts on
how things should be put together.

What finally pushed this game into something which I felt was finally
ready, was the London Mathematical Society, who invited me to give
a course as part of their 2024 Summer School at the University of Essex.
I chose to give a course on filters, and made this game as part of
the learning experience for the students.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels."
Prerequisites "Knowledge of some basic Lean tactics" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
