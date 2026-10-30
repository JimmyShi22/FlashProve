-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ToyDescriptions.lean: at the library's examples of the two small test protocols, the
program's description is the library's.

The library has descriptions of the chains of the test protocols "product" and "links" at the sizes
of two editions each, and theorems about them. The program makes its own description from a chain's
parameter bytes and from the dry run of the protocol's block. This file proves that, under the
parameter bytes of one of the library's descriptions, a description that the program makes is that
description. The
digest of the public file stays a symbol throughout: no hash is evaluated.

Main definitions: `agrees`, `givenOf`, `productOf`, `linksOf`.
Main statements: `Given.read_spelled`, `spec_of_agrees`, `product_spec_tiny`, `product_spec_full`,
`links_spec_tiny`, `links_spec_full`.
What is not claimed: that these parameter bytes are the bytes of the C++ programs' own files. That
is a test in the library, no theorem.
-/
import Fmt.M1SpecKnownProofs
import Fmt.M2Theirs
import OnBytes.Params.EntryRoundsToy
import OnBytes.Toy.Links
import OnBytes.Toy.Product

namespace OnBytes.Params

/-- Parameter bytes that were spelled from a plan, a digest and items are read back as these, if the
three fit their spelling (`Fmt.Params.fit`), the plan is in order and all its names are names of the
format. -/
theorem Given.read_spelled (P : Fmt.Plan) (cfg : ByteArray) (items : List (String × ByteArray))
    (hfit : (⟨P, cfg, items⟩ : Fmt.Params).fit = true) (hok : (P.ok && namesKnown P) = true) :
    Given.read (Fmt.paramsBytes P cfg items) =
      some ⟨Fmt.paramsBytes P cfg items, P, cfg, items⟩ := by
  have h : Fmt.paramsRead (Fmt.paramsBytes P cfg items) = some ⟨P, cfg, items⟩ :=
    Fmt.params_back ⟨P, cfg, items⟩ hfit
  unfold Given.read
  rw [paramsReadT_eq, h]
  show (if (P.ok && namesKnown P) = true then _ else none) = _
  rw [if_pos hok]

/-- True if the dry run of a block from a start returns the given rounds and opens no stored
tree. -/
def agrees (b : Blk Unit) (s : Start) (rounds : List Fmt.Round) : Bool :=
  match b.rounds s with
  | none => false
  | some r =>
    decide (r.map (fun x => roundParts x.1) = rounds.map roundParts) &&
      decide (r.map (·.2) = rounds.map fun _ => [])

/-- If the dry run agrees with given rounds, the description that is made of it is the plain
description with these rounds. -/
theorem spec_of_agrees {b : Blk Unit} {s : Start} {rounds : List Fmt.Round} {g : Given}
    {label : Nat} {r : Rounds} {S : Fmt.SpecX} (ha : agrees b s rounds = true)
    (hr : b.rounds s = some r) (hd : describeWith g label ByteArray.empty .inFile r = some S) :
    S = Fmt.SpecX.plain { label := label, plan := g.plan, params := g.bytes,
                          statement := ByteArray.empty, rand := .inFile, firstTree := 0,
                          cfg := g.cfg, rounds := rounds } := by
  unfold agrees at ha
  rw [hr] at ha
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
  have h1 : r.map (·.1) = rounds := rounds_of_parts (by rw [List.map_map]; exact ha.1)
  rw [Given.describe_eq hd, h1, ha.2]
  rfl

/-- A property of all values that the second step of two can return holds of what the two steps
return. -/
theorem of_bind {α β : Type} {good : β → Prop} {x : Option α} {f : α → Option β}
    (hf : ∀ a b, f a = some b → good b) : ∀ b, x.bind f = some b → good b := by
  intro b h
  cases x with
  | none => cases h
  | some a => exact hf a b h

/-! ## The run "product" -/

/-- The names of the items of a run "product". -/
def productNames : List String :=
  ["codes", "the oracle message a, b, c", "the stages of the proximity test",
    "the choices of the proximity test"]

/-- What `Toy.ProductPublic.read` makes of parameter bytes that have been read. -/
def productOf (g : Given) : Option Toy.ProductPublic :=
  if g.plan.field != .two then none
  else if g.itemNames != productNames then none
  else
    (g.item "codes").bind fun a => (readCodes a).bind fun codes =>
    (g.item "the oracle message a, b, c").bind fun b => (readNotice b).bind fun notice =>
    (g.item "the stages of the proximity test").bind fun c => (readStages c).bind fun stages =>
    (g.item "the choices of the proximity test").bind fun d => (readFlag d).bind fun ride =>
    some ⟨g, codes, notice, stages, ⟨ride⟩⟩

/-- The reader of a run's parameter bytes reads the bytes and then does this. -/
theorem product_read (b : ByteArray) :
    Toy.ProductPublic.read b = (Given.read b).bind productOf := by
  unfold Toy.ProductPublic.read
  cases Given.read b with
  | none => rfl
  | some g =>
    show _ = productOf g
    unfold productOf productNames
    by_cases h1 : (g.plan.field != .two) = true
    · have n1 : g.plan.field ≠ Fmt.Fld.two := by simpa using h1
      simp [n1]
    · by_cases h2 : (g.itemNames != ["codes", "the oracle message a, b, c",
          "the stages of the proximity test", "the choices of the proximity test"]) = true
      · have e1 : g.plan.field = Fmt.Fld.two := by simpa using h1
        have n2 : g.itemNames ≠ ["codes", "the oracle message a, b, c",
            "the stages of the proximity test", "the choices of the proximity test"] := by
          simpa using h2
        simp [e1, n2]
      · have e1 : g.plan.field = Fmt.Fld.two := by simpa using h1
        have e2 : g.itemNames = ["codes", "the oracle message a, b, c",
            "the stages of the proximity test", "the choices of the proximity test"] := by
          simpa using h2
        simp [e1, e2]

/-- What it returns holds what was read. -/
theorem productOf_given (g : Given) : ∀ p, productOf g = some p → p.given = g := by
  unfold productOf
  split
  · intro p h
    cases h
  · split
    · intro p h
      cases h
    · repeat (apply of_bind; intro _)
      intro p h
      cases h
      rfl

/-- Parameters fit their spelling if the plan fits, the digest has 32 bytes and the items fit. -/
theorem fit_of {P : Fmt.Plan} {cfg : ByteArray} {items : List (String × ByteArray)}
    (h1 : P.fit = true) (h2 : cfg.size = 32)
    (h3 : (items.all fun x => Fmt.nameFit x.1 && decide (x.2.size < 2 ^ 64)) = true) :
    (⟨P, cfg, items⟩ : Fmt.Params).fit = true := by
  show (P.fit && cfg.size == 32 &&
    items.all fun x => Fmt.nameFit x.1 && decide (x.2.size < 2 ^ 64)) = true
  rw [h1, h2, h3]
  rfl

/-- What parameter bytes that were spelled from a description's plan and digest and from items
hold. -/
def givenOf (S : Fmt.Spec) (items : List (String × ByteArray)) : Given :=
  ⟨Fmt.paramsBytes S.plan S.cfg items, S.plan, S.cfg, items⟩

/-- The run "product". Let S be a description with the label 1, no statement, its random bytes in
the file and no tree before its own, whose parameter bytes spell its plan, its digest and some
items. If these three fit their spelling, the plan is in order with names of the format, and the dry
run of the program's block under these bytes agrees with S's rounds (`agrees`), then a chain that
the program makes from these parameter bytes has the description S. -/
theorem product_spec_of (S : Fmt.Spec) (items : List (String × ByteArray))
    (hS : S = { label := 1, plan := S.plan, params := Fmt.paramsBytes S.plan S.cfg items,
                statement := ByteArray.empty, rand := .inFile, firstTree := 0, cfg := S.cfg,
                rounds := S.rounds })
    (hfit : (⟨S.plan, S.cfg, items⟩ : Fmt.Params).fit = true)
    (hok : (S.plan.ok && namesKnown S.plan) = true)
    (ha : ((productOf (givenOf S items)).any fun p => agrees p.block p.start S.rounds) = true)
    {c : Chain Unit} (h : (Toy.ProductPublic.read S.params).bind Toy.productChain = some c) :
    c.spec = Fmt.SpecX.plain S := by
  have hp : S.params = Fmt.paramsBytes S.plan S.cfg items := congrArg (·.params) hS
  rw [product_read, hp, Given.read_spelled _ _ _ hfit hok] at h
  change ((productOf (givenOf S items)).bind Toy.productChain) = some c at h
  cases hq : productOf (givenOf S items) with
  | none => rw [hq] at h; cases h
  | some p =>
    rw [hq] at h ha
    have hg : p.given = givenOf S items := productOf_given _ p hq
    have ha' : agrees p.block p.start S.rounds = true := ha
    change Toy.productChain p = some c at h
    unfold Toy.productChain at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, X, hd, rfl⟩ := h
    show X = _
    rw [spec_of_agrees ha' hr hd, hg]
    exact congrArg Fmt.SpecX.plain hS.symm

/-- A chain that the program makes from the parameter bytes of the library's description of the run
"product", tiny edition, has that description. -/
theorem product_spec_tiny {c : Chain Unit}
    (h : (Toy.ProductPublic.read Fmt.M1.Theirs.specTiny.params).bind Toy.productChain = some c) :
    c.spec = Fmt.SpecX.plain Fmt.M1.Theirs.specTiny :=
  product_spec_of Fmt.M1.Theirs.specTiny (Fmt.M1.itemsOf Fmt.M1.Theirs.sizesTiny) rfl
    (fit_of (by decide +kernel) (Fmt.M1.size_configDigest _) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) h

/-- The same at the library's full edition of the run "product". -/
theorem product_spec_full {c : Chain Unit}
    (h : (Toy.ProductPublic.read Fmt.M1.Theirs.specFull.params).bind Toy.productChain = some c) :
    c.spec = Fmt.SpecX.plain Fmt.M1.Theirs.specFull :=
  product_spec_of Fmt.M1.Theirs.specFull (Fmt.M1.itemsOf Fmt.M1.Theirs.sizesFull) rfl
    (fit_of (by decide +kernel) (Fmt.M1.size_configDigest _) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) h

/-! ## The run "links" -/

/-- What `Toy.LinksPublic.read` makes of parameter bytes that have been read. -/
def linksOf (g : Given) : Option Toy.LinksPublic :=
  if g.plan.field != .two then none
  else if g.itemNames != ["codes", "the chain of links"] then none
  else
    (g.item "codes").bind fun a => (readCodes a).bind fun codes =>
    (g.item "the chain of links").bind fun b => (readReq b).bind fun shape =>
    some ⟨g, codes, shape⟩

/-- The reader of a run's parameter bytes reads the bytes and then does this. -/
theorem links_read (b : ByteArray) : Toy.LinksPublic.read b = (Given.read b).bind linksOf := by
  unfold Toy.LinksPublic.read
  cases Given.read b with
  | none => rfl
  | some g =>
    show _ = linksOf g
    unfold linksOf
    by_cases h1 : (g.plan.field != .two) = true
    · have n1 : g.plan.field ≠ Fmt.Fld.two := by simpa using h1
      simp [n1]
    · by_cases h2 : (g.itemNames != ["codes", "the chain of links"]) = true
      · have e1 : g.plan.field = Fmt.Fld.two := by simpa using h1
        have n2 : g.itemNames ≠ ["codes", "the chain of links"] := by simpa using h2
        simp [e1, n2]
      · have e1 : g.plan.field = Fmt.Fld.two := by simpa using h1
        have e2 : g.itemNames = ["codes", "the chain of links"] := by simpa using h2
        simp [e1, e2]

/-- What it returns holds what was read. -/
theorem linksOf_given (g : Given) : ∀ p, linksOf g = some p → p.given = g := by
  unfold linksOf
  split
  · intro p h
    cases h
  · split
    · intro p h
      cases h
    · repeat (apply of_bind; intro _)
      intro p h
      cases h
      rfl

/-- The run "links": as `product_spec_of`, with the label 2 and the block of that run. -/
theorem links_spec_of (S : Fmt.Spec) (items : List (String × ByteArray))
    (hS : S = { label := 2, plan := S.plan, params := Fmt.paramsBytes S.plan S.cfg items,
                statement := ByteArray.empty, rand := .inFile, firstTree := 0, cfg := S.cfg,
                rounds := S.rounds })
    (hfit : (⟨S.plan, S.cfg, items⟩ : Fmt.Params).fit = true)
    (hok : (S.plan.ok && namesKnown S.plan) = true)
    (ha : ((linksOf (givenOf S items)).any fun p => agrees p.block p.start S.rounds) = true)
    {c : Chain Unit} (h : (Toy.LinksPublic.read S.params).bind Toy.linksChain = some c) :
    c.spec = Fmt.SpecX.plain S := by
  have hp : S.params = Fmt.paramsBytes S.plan S.cfg items := congrArg (·.params) hS
  rw [links_read, hp, Given.read_spelled _ _ _ hfit hok] at h
  change ((linksOf (givenOf S items)).bind Toy.linksChain) = some c at h
  cases hq : linksOf (givenOf S items) with
  | none => rw [hq] at h; cases h
  | some p =>
    rw [hq] at h ha
    have hg : p.given = givenOf S items := linksOf_given _ p hq
    have ha' : agrees p.block p.start S.rounds = true := ha
    change Toy.linksChain p = some c at h
    unfold Toy.linksChain at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, X, hd, rfl⟩ := h
    show X = _
    rw [spec_of_agrees ha' hr hd, hg]
    exact congrArg Fmt.SpecX.plain hS.symm

/-- A chain that the program makes from the parameter bytes of the library's description of the run
"links", tiny edition, has that description. -/
theorem links_spec_tiny {c : Chain Unit}
    (h : (Toy.LinksPublic.read Fmt.M2.Theirs.specTiny.params).bind Toy.linksChain = some c) :
    c.spec = Fmt.SpecX.plain Fmt.M2.Theirs.specTiny :=
  links_spec_of Fmt.M2.Theirs.specTiny (Fmt.M2.itemsOf Fmt.M2.tinyPar) rfl
    (fit_of (by decide +kernel) (Fmt.M1.size_configDigest _) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) h

/-- The same at the library's full edition of the run "links". -/
theorem links_spec_full {c : Chain Unit}
    (h : (Toy.LinksPublic.read Fmt.M2.Theirs.specFull.params).bind Toy.linksChain = some c) :
    c.spec = Fmt.SpecX.plain Fmt.M2.Theirs.specFull :=
  links_spec_of Fmt.M2.Theirs.specFull (Fmt.M2.itemsOf Fmt.M2.toyPar) rfl
    (fit_of (by decide +kernel) (Fmt.M1.size_configDigest _) (by decide +kernel))
    (by decide +kernel) (by decide +kernel) h

end OnBytes.Params
