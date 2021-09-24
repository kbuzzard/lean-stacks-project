# IMPORTANT

This project is deprecated. It was joint work by me (Kevin Buzzard), Kenny Lau and Chris Hughes. It was our first attempt to do MSc level mathematics in Lean (back in 2017/18) and we made some poor design decisions due to inexperience. Once I had understood better how to write this project, I supervised Ramon Fernandez Mir's [masters project](https://github.com/ramonfmir/lean-scheme) which achieved everything this repo achieved and more too, and better. I would look there instead.

# lean-stacks-project
 Formal verification of parts of the Stacks Project in Lean 

# Getting it working

Here's the old-fashioned way, using `leanpkg`.

First install Lean (at the time of writing, the version you need is
the nightly of 2018-04-06).

Then clone the project onto your computer e.g. with `git clone git@github.com:kbuzzard/lean-stacks-project.git`.

Then change into the project directory, e.g. with `cd lean-stacks-project/`

Then type `leanpkg configure` (with the 2018-04-06 `leanpkg` of course). This will (amongst other things) create a `leanpkg.path` file.

Then you probably don't need to type `leanpkg upgrade` but it won't do any harm.

Then you can type `leanpkg build`. At the time of writing you'll get errors in `scheme.lean` and maybe in a few other places, because I don't have any branches and the project is still a work in progress.
