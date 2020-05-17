# Derivations of Lenses
Understanding lenses by making them from scratch in different ways.

- 2020-04-23 Added `GetterSetterPair.hs`
  - Direct representation of lenses as a pair of getters and setters,
    however, they do not compose, which poses problems when one tries
    to build larger lenses out of smaller ones.
- 2020-04-24 Added `VanLaarhoven.hs`
  - A CPS encoding of lenses, representing them as functions, allowing
    for lens composition with `(.)`.
- 2020-04-25 Added `ProfunctorOptics.hs`
  - A profunctor encoding of optics, allowing for lens composition
    with `(.)`.  Recovering lenses, prisms, traversals arises from
    imposing additional constraints on the profunctor.

# Resources
## Talks
- Jeremy Gibbons, _Profunctor Optics - Modular Data Accessors_
  [Link](https://www.youtube.com/watch?v=sfWzUMViP0M)
- Bartosz Milewski, _Profunctor Optics: The Categorical
  Approach_ [Link](https://www.youtube.com/watch?v=l1FCXUi6Vlw)

## Blog posts
Joseph Abrahamson, _Lenses from scratch_
[Link](https://www.schoolofhaskell.com/user/tel/lenses-from-scratch)

## Books
Chris Penner, _Optics By Example_
[Link](https://leanpub.com/optics-by-example)
