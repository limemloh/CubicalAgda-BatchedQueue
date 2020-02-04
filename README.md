# Case Study: BatchedQueue
A Cubical Agda case study, implementing an immutable FIFO queue using Higher
Inductive Types to capture higher structure.

The queue is called BatchedQueue and is describe by _Chris Okasaki_ in chapter
5.2 of his book _Purely Functional Data Structures_ (Cambridge University Press,
New York, NY, USA, 1999.).

The case study was a part of a project work done by
[@paldepind](https://github.com/paldepind) and
[@limemloh](https://github.com/limemloh) in Fall 2019.

## Gettting started
Install [Agda](https://github.com/agda/agda) and the [Cubical](https://github.com/agda/cubical) library using git.

In order to use the Cubical Agda in our files, we have created an `.agda-lib` describing `cubical` as a dependency.
To tell agda where to find the library, you need to add a path in a file `~/.agda/libraries`, which you might have to create yourself.
The path to add is the one for the `cubical.agda-lib` found in the Cubical repo.

Such that `~/.agda/libraries` look like this:
```
/path/to/cubical/cubical.agda-lib
```

Test by running `C-c C-l` in `BatchedQueue.agda`
