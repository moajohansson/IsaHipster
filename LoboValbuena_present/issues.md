Schematic type variables arising with constants (in parameterised types)

- It is a question whether to add all rules related to definitions or not (not only simps, but elims, distinct, exhaust, etc.)
  They can save inductions, although if discovered in theory exploration it would not be much on an issue

- routine_tacs : do they get all these definitional rules?
  But how very "routinary" is it if we have to specify them?

- something bad is we are ultimately suggesting things to besolved by induction which could probably do without
  However, maybe that is reasonable after all. It is structural, it is founded in a stronger and closer way to how we write programs, how we structure them and manage datatypes
  Whilst using FO proving is based more on logic theory, which is reasonable and a legit tool, maybe using it as little as possible is favourable?
  We use it too, but we could aim to minimise its use? MOTIVATE

- We reduce rules by inducting too


