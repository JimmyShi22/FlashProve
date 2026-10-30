-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedSeam.lean: the rule of composition for the shared chain, in the very form
in which the top theorem for a proof file asks it: of the second chain's reduction in the library's
row of a file's three chains. A SHEET OF STATEMENTS: five propositions written as `def … : Prop`,
and controls of form. NOTHING IS PROVED IN THIS FILE.

The setting. Johnson/Desc/Sound/FileRule.lean lays the three chains' folds into the library's row
(`Three.row`: `rowOf`, OnBytes/Maker/Row.lean) and names the data of which the three clauses of
soundness speak (`Three.snd`). The top theorem for a proof file (`proofSound_top_links`,
Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean) asks of that value, for a batch of N requests, the list
`Links.KnowsJ` (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean); its field l₂ is a link with keys over the second
chain's reduction. That reduction is not the chain's fold as it stands. It has a round in front that
the fold does not read (the joining round, behind a test okJ on what it sends); it makes the fold's
first record of what the first chain has handed on (`in₂`); and it packs the fold's last record with
that (`out₂`).

What is said. `SeamLink`: if the three rows of pieces are the file's three chains (`Three.Fits`),
every block of the shared chain is a link of the batch along some keys (`Keyed`,
Johnson/Desc/Sound/SharedRule.lean), what is claimed of what the second chain hands on implies what
is claimed at its last boundary (`Three.Glue₂`), the key k₁ of what the first chain hands on
determines the key at the shared chain's first boundary, and the key k₂ of what the second chain
hands on is a function of k₁ and of the key at the shared chain's last boundary, THEN the field l₂
holds at that value: at the blocks' errors in a row, each once, behind an error 0 for the joining
round. `SeamOfGood`: the same from a law for one request for each block (`EachGoodIn`,
Johnson/Desc/Sound/GoodIn.lean), where the shared chain's record holds, beside the chain's own part,
what was handed to the chain, the blocks are lifted, and the relations are "Ra and Rc": Ra reads the
chain's own part, the stored table and the chain's own trees; Rc is what each request carries past
the chain. There k₁ is the chain's own first record with the stored table. `RunOfStarts₁`,
`RunOfStarts`, `RunOfStarts₃`: in the filling that is meant (`Three.ofStarts`, lifted blocks, each
with the test that every word is below the prime) the three chains' runs ARE: that test; the fold of
the chain's own blocks from the chain's own first record; and the last own record packed behind what
was handed to the chain.

Limits. (1) Those of SharedRule.lean, GoodIn.lean and FileRule.lean. (2) THE LAW ON k₁ IS THE HEART
OF THE MATTER: l₂ speaks of the batches whose slots have one k₁, and the field l₁ of the same list
asks that k₁ is common to all slots with one external word: so the shared chain's own first record
must not hang on what differs between the requests of a batch. Nothing here shows that. At a k₁ that
tells all statements apart l₂ holds and l₁ cannot. (3) The fields l₁ and l₃ are binders in the
example. (4) The top theorem asks the list record by record, behind `Links.comap`: that step is not
here.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRule
import Johnson.Desc.Sound.FileRule
import OnBytes.TypedOracleCompiler.Joined.MidLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

/-- **The shared chain's clause for a batch, at the library's row of the three folds.** kA, kZ: the
keys at the shared chain's first and last boundary. k₁, k₂: the keys of what the first and the
second chain hand on. -/
def SeamLink : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ : Type)
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂) (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
    (N : ℕ) (kA kZ : BKey (frameAt D all D.key₂ T.ft₂) S₂) (k₁ : X₁ × (EAll D all).Str → κ₁)
    (k₂ : X₂ × (EAll D all).Str → κ₂),
    T.Fits → Keyed N Q.on₂ Q.R₂ 0 T.p₂ T.l₂ kA kZ → T.Glue₂ Q →
    (∃ g : κ₁ → kA.1, ∀ a, kA.2 (T.in₂ a.1, a.2) = g (k₁ a)) →
    (∃ G : κ₁ → kZ.1 → κ₂, ∀ a b, k₂ (T.out₂ a.1 b.1, b.2) = G (k₁ a) (kZ.2 b)) →
    LinkJ ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₂
      (chainsOf C D tF tJ t3).A₂ N k₁ k₂ (fun _ => True) (T.mid₁ Q) (T.mid₂ Q)
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).e₂ (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₂

/-- **The same from a law for one request for each block.** `get`, `set`: the chain's own part of
its record. Ra: the relations that read the statement through the chain's own part of the record,
the stored table and the chain's own trees. Rc: what each request carries past the chain. The key
k₁: the chain's own first record, with the stored table. The key behind is trivial. -/
def SeamOfGood : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁ S₂ S₀ S₃ X₁ X₂ Cl W TF TJ T3 : Type)
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)
    (Q : Places D all S₁ S₂ S₃ W) (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂) (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃)
    (N : ℕ) (get : S₂ → S₀) (set : S₂ → S₀ → S₂) (Ra : ℕ → S₂ × (EAll D all).Str → W → Prop)
    (Rc : S₂ × (EAll D all).Str → W → Prop),
    T.Fits → (Q.R₂ = fun i a w => Ra i a w ∧ Rc a w) →
    EachGoodIn Q.on₂ Ra 0 (T.p₂ :: T.l₂) →
    EachRels Q.on₂ Ra (actsOf get D.t₁ T.p₂ T.l₂) 0 (T.p₂ :: T.l₂) →
    EachKeeps Q.on₂ Rc 0 (T.p₂ :: T.l₂) → (∀ t s, get (set t s) = s) →
    (∀ t s s', set (set t s) s' = set t s') →
    (∀ q ∈ T.p₂ :: T.l₂, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
    (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) → T.Glue₂ Q →
    LinkJ ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₂
      (chainsOf C D tF tJ t3).A₂ N
      (fun a : X₁ × (EAll D all).Str => (get (T.in₂ a.1), a.2.1)) (fun _ => ()) (fun _ => True)
      (T.mid₁ Q) (T.mid₂ Q) (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).e₂
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₂

/-- **The first chain's run in the filling that is meant** (`Three.ofStarts`). bs: the chain's own
blocks, typed at the chain's own record. The pieces hold these blocks, each with the test that every
word is below the prime (`below`), lifted to the pair of what was handed to the chain and the
chain's own record. back: the rounds that are put back behind those shown (the empty round that
closes the first chain). An equation of functions. -/
def RunOfStarts₁ : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁' S₂' S₃' X₁ X₂ Cl W P : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (bs : List (Block S₁' Cl)) (back : List Fmt.RoundView),
    (T.p₁ :: T.l₁).map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) →
    rowBack T.p₁ T.l₁ = back → viewWordsBelowPrime ⟨back, []⟩ = true →
    (T.ofStarts pub start₁ start₂ start₃).run₁ = fun x v =>
      if viewWordsBelowPrime v then
        (foldRun (frameAt D all D.key₁ T.ft₁) T.n₁ bs back (start₁ (pub x)) v).map fun s =>
          (pub x, s)
      else none

/-- **The second chain's.** It starts from the public part alone; its last own record is packed
behind what was handed on. -/
def RunOfStarts : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁' S₂' S₃' X₁ X₂ Cl W P : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (bs : List (Block S₂' Cl)),
    (T.p₂ :: T.l₂).map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) →
    rowBack T.p₂ T.l₂ = [] →
    (T.ofStarts pub start₁ start₂ start₃).run₂ = fun a v =>
      if viewWordsBelowPrime v then
        (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ bs [] (start₂ a.1) v).map fun s =>
          (a.1, a.2, s)
      else none

/-- **The third chain's.** It says yes where every word is below the prime, the chain has a first
own record, and the fold from it returns. -/
def RunOfStarts₃ : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y S₁' S₂' S₃' X₁ X₂ Cl W P : Type) (pub : Y → P)
    (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (bs : List (Block S₃' Cl)),
    (T.p₃ :: T.l₃).map (·.b) = (bs.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) →
    rowBack T.p₃ T.l₃ = [] →
    (T.ofStarts pub start₁ start₂ start₃).run₃ = fun a v =>
      viewWordsBelowPrime v && ((start₃ a.1 a.2.1 a.2.2).bind fun s =>
                    foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ bs [] s v).isSome


-- THE FEED: the statement's conclusion is laid, as it stands, into the field l₂ of the list that
-- the top theorem asks for a batch; the two hand-overs are free, since every statement counts
example (hS : SeamLink) (C : CK) (D : WholeD) (all : List LeftT)
    (Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (Q : Places D all S₁ S₂ S₃ W)
    (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool)
    (h₁ : (rowIOR T.p₁ T.l₁).shape = uLT C D.ds₁) (h₂ : (rowIOR T.p₂ T.l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR T.p₃ T.l₃).shape = uLT C D.ds₃) (N : ℕ)
    (kA kZ : BKey (frameAt D all D.key₂ T.ft₂) S₂) (k₁ : X₁ × (EAll D all).Str → κ₁)
    (k₂ : X₂ × (EAll D all).Str → κ₂) (hF : T.Fits)
    (hk : Keyed N Q.on₂ Q.R₂ 0 T.p₂ T.l₂ kA kZ) (hG : T.Glue₂ Q)
    (law₁ : ∃ g : κ₁ → kA.1, ∀ a, kA.2 (T.in₂ a.1, a.2) = g (k₁ a))
    (law₂ : ∃ G : κ₁ → kZ.1 → κ₂, ∀ a b, k₂ (T.out₂ a.1 b.1, b.2) = G (k₁ a) (kZ.2 b))
    (l₁ : LinkJ ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁
      (chainsOf C D tF tJ t3).A₁ N Prod.snd k₁
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).on₀ (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).R₀
      (T.mid₁ Q) (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).e₁
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₁)
    (l₃ : LinkJ ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₃
      (chainsOf C D tF tJ t3).A₃ N k₂ (fun _ : Unit => ()) (fun _ => True) (T.mid₂ Q)
      (fun _ _ => True) (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).e₃
      (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃).ε₃) :
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).KnowsJ N k₁ k₂ :=
  ⟨l₁, hS C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N kA kZ k₁
    k₂ hF hk hG law₁ law₂, l₃, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

-- THE VALUE: in the filling that is meant the library's row is, by these three equations, the row
-- at the three runs as they were agreed
example (h₁ : RunOfStarts₁) (h₂ : RunOfStarts) (h₃ : RunOfStarts₃) (C : CK) (D : WholeD)
    (all : List LeftT) (Y S₁' S₂' S₃' X₁ X₂ Cl W P TF TJ T3 : Type) (tF : TF) (tJ : TJ) (t3 : T3)
    (pub : Y → P) (start₁ : P → S₁') (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
    (bs₁ : List (Block S₁' Cl)) (bs₂ : List (Block S₂' Cl)) (bs₃ : List (Block S₃' Cl))
    (back : List Fmt.RoundView) (okF : Y → TF → Bool) (okJ : P × S₁' → TJ → Bool)
    (ok3 : P × S₁' × S₂' → T3 → Bool)
    (b₁ : (T.p₁ :: T.l₁).map (·.b) =
      (bs₁.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (b₂ : (T.p₂ :: T.l₂).map (·.b) =
      (bs₂.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (b₃ : (T.p₃ :: T.l₃).map (·.b) =
      (bs₃.map below).map (Block.lift Prod.snd fun t s => (t.1, s)))
    (k₁ : rowBack T.p₁ T.l₁ = back) (kb : viewWordsBelowPrime ⟨back, []⟩ = true)
    (k₂ : rowBack T.p₂ T.l₂ = []) (k₃ : rowBack T.p₃ T.l₃ = []) :
    (T.ofStarts pub start₁ start₂ start₃).row tF tJ t3 okF okJ ok3 =
      rowOf C D tF tJ t3 all all okF okJ ok3
        (fun x v =>
          if viewWordsBelowPrime v then
            (foldRun (frameAt D all D.key₁ T.ft₁) T.n₁ bs₁ back (start₁ (pub x)) v).map fun s =>
              (pub x, s)
          else none)
        (fun a v =>
          if viewWordsBelowPrime v then
            (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ bs₂ [] (start₂ a.1) v).map fun s =>
              (a.1, a.2, s)
          else none)
        (fun a v =>
          viewWordsBelowPrime v && ((start₃ a.1 a.2.1 a.2.2).bind fun s =>
                        foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ bs₃ [] s v).isSome) := by
  unfold Three.row
  rw [h₁ C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs₁ back b₁ k₁ kb,
    h₂ C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs₂ b₂ k₂,
    h₃ C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs₃ b₃ k₃]

end VerifiableInference.Desc.Sound
