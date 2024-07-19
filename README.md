# The Filter Game

## Status: prerelease

A work-in-progress game teaching the definition of a filter.

Developed as part of the 2024 London Mathematical Society summer school,
held at the University of Essex.

## Editing the game

### Remote running via GitPod

You don't need to install anything onto your computer using this method.

Just click here: [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)
](https://gitpod.io/#https://github.com/kbuzzard/FilterGame)

### Remote running via Codespaces

You don't need to install anything onto your computer using this method.

Go to the project's [home page on GitHub](https://github.com/kbuzzard/FilterGame),
click "Code" and then "Codespaces" so it looks like this:

Pic: ![codespaces installation](png/codespaces.png?raw=true "codespaces installation")

Then click "create codespace on main", and then wait for a few minutes. When it looks like everything has downloaded, open up the `IIScExperiments` directory (not the file!) and the code I've been using in the lectures should just work.

Note to self: I got codespaces working by adding the files `.devcontainer/devcontainer.json` and `.devcontainer/Dockerfile`.

### Local installation

### Local installation

First install Lean 4 following the instructions [here](https://leanprover.github.io/lean4/doc/quickstart.html).

Then download and install this project by going to its [home page on GitHub](https://github.com/kbuzzard/FilterGame),
clicking "Code" and "local", and then downloading the project onto your computer.

Pic: ![local installation](png/codelocal.png?raw=true "local installation")

Next find `TERMINAL` in the bottom panel of VS Code, type `lake exe cache get`, and wait until all files are downloaded and installed and your cursor has reappeared.

Next, open the *project folder* in VS Code. This folder is called `FilterGame`.
