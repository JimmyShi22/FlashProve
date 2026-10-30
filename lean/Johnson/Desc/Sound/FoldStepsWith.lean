-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/FoldStepsWith.lean: THE TRACE (Johnson/Desc/Sound/FoldSteps.lean) FOR A FOLD IN
WHICH THE CLAIMS ARE GATHERED BY A BLOCK's OWN TABLE, NOT BY THE LINK's ORDER: general in the list
of blocks, in the block B that gathers, IN THE GATHERER f, AND IN ITS TYPE OF CLAIMS, which need not
be the fold's. Statements, written as `def … : Prop`, with their proofs.

Why. In a version of the descriptions the link's field `batch` does not read the
function of claims that `Link.blocksInOrder` hands it; the fold's type of claims is Unit and the lots' blocks
state no run; the adding is done inside the batching's place, by blocks that call a gatherer of
their own over a SECOND MAKE of the kinds' blocks, at the type Claim (by report).
So `claimsIn L.hear L.order` is run by nobody there, and `LinkTraceAt` has no payer. What a
kind's law wants of the fold is had all the same, of the gatherer that does run.

  `CallsWith R Q B f`: `CallsAt`, with the claims' type free.
  `callsWithRight`, `callsWithLeft`: through `Block.andThen`: the other half steps R.
  `TracedWith`: what is said of a fold over pre ++ b :: (mid ++ B :: rest) from (s, rs, cols), AT
    ANY GATHERER f: t, t₁, u₀, z are values of folds over named fronts; b's and B's decisions went
    on at their own stretches; R t₁ u₀; B called f at u: R u₀ u; it went on, to cls and e; R e z; Q.
  `FoldTraceWith`, `foldTraceWith`: the blocks of mid step R; `CallsWith R Q B f`: then every fold
    that goes on is traced so.
  `RunIn R run u e cls`: one run was called between u and e, its claims among cls: WHAT A GATHERER's
    OWN LAW GIVES of each of its runs. `runInOfClaimsIn`: Block.lean's `claimsIn` has it, over any
    list of blocks.
  `RanWith`, `ranWith`: at `Carries`: if b's decision left g as heard and a ledger F' with its
    sizes: a run that is `RunIn` and carries `RanAt` … g F' …, leaving a ledger G with `later G H`,
    H the ledger at any record x to which e carries; g is still heard there.

Every "there is", walked: as in FoldSteps.lean's head.

Limits. Tools: no block of the protocol is named here. NOTHING TIES THE GATHERER's RUNS TO THE
FOLD's BLOCKS: that a run is the run of the kind whose decision b's is, is said by whoever lays the
two makes. Several blocks that gather, each a stretch of the order: one trace a block. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StepsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl Cl' : Type}

/-- Where B's decision goes on, f was called. The claims' type is f's own. -/
def CallsWith (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop)
    (B : Block S Cl) (f : S → Except String (List Cl' × S)) : Prop :=
  ∀ s rs gs s', B.decide s rs gs = .ok s' →
    ∃ t cls e, R s t ∧ f t = .ok (cls, e) ∧ R e s' ∧ Q s rs t cls e s'

/-- No word on what was done with the claims. -/
def QAny : S → List Fmt.RoundView → S → List Cl' → S → S → Prop := fun _ _ _ _ _ _ => True

/-- Behind a block that steps. -/
theorem callsWithRight {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : p.Steps R) (hq : CallsWith R Q q f) : CallsWith R QAny (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, -⟩ := hq _ _ _ _ H'
  exact ⟨t, cls, e, hR.trans _ _ _ (hp _ _ _ _ hm) h₁, h₂, h₃, trivial⟩

/-- In front of a block that steps. -/
theorem callsWithLeft {R : S → S → Prop} {Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop}
    (hR : Pre R) (name : String) (p q : Block S Cl) (f : S → Except String (List Cl' × S))
    (hp : CallsWith R Q p f) (hq : q.Steps R) : CallsWith R QAny (p.andThen name q) f := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨t, cls, e, h₁, h₂, h₃, -⟩ := hp _ _ _ _ hm
  exact ⟨t, cls, e, h₁, h₂, hR.trans _ _ _ h₃ (hq _ _ _ _ H'), trivial⟩

/-- One run was called between the records u and e, and its claims are among cls. -/
def RunIn (R : S → S → Prop) (run : Nat → S → Except String (List Cl' × S)) (u e : S)
    (cls : List Cl') : Prop :=
  ∃ n v cl v', run n v = .ok (cl, v') ∧ R u v ∧ R v' e ∧ ∀ c ∈ cl, c ∈ cls

/-- What `FoldTraceWith` says of a fold over pre ++ b :: (mid ++ B :: rest) from (s, rs, cols), at a
gatherer f. -/
structure TracedWith (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop)
    (pre mid : List (Block S Cl)) (b B : Block S Cl) (f : S → Except String (List Cl' × S))
    (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (t t₁ u₀ z u e : S)
    (cls : List Cl') : Prop where
  front : ∃ c, foldBlocks ft pre s rs cols = .ok (t, behindOf pre rs, c)
  decided : ∃ gs, b.decide t (shownAt pre b rs) gs = .ok t₁
  behindB : ∃ c, foldBlocks ft (pre ++ [b]) s rs cols = .ok (t₁, behindOf (pre ++ [b]) rs, c)
  heard : ∃ c, foldBlocks ft (pre ++ [b] ++ mid) s rs cols =
    .ok (u₀, behindOf (pre ++ [b] ++ mid) rs, c)
  toGather : R t₁ u₀
  gathered : ∃ gs, B.decide u₀ (shownAt (pre ++ [b] ++ mid) B rs) gs = .ok z
  behindGather : ∃ c, foldBlocks ft (pre ++ [b] ++ mid ++ [B]) s rs cols =
    .ok (z, behindOf (pre ++ [b] ++ mid ++ [B]) rs, c)
  toCall : R u₀ u
  called : f u = .ok (cls, e)
  fromCall : R e z
  said : Q u₀ (shownAt (pre ++ [b] ++ mid) B rs) u cls e z

def FoldTraceWith : Prop :=
  ∀ (S Cl Cl' : Type) (R : S → S → Prop) (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop),
    Pre R → ∀ (pre mid rest : List (Block S Cl)) (b B : Block S Cl)
    (f : S → Except String (List Cl' × S)),
    (∀ c ∈ mid, c.Steps R) → CallsWith R Q B f →
    ∀ (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft (pre ++ b :: (mid ++ B :: rest)) s rs cols = .ok out →
      ∃ t t₁ u₀ z u e cls, TracedWith R Q pre mid b B f ft s rs cols t t₁ u₀ z u e cls

theorem foldTraceWith : FoldTraceWith := by
  intro S Cl Cl' R Q hR pre mid rest b B f hs hcall ft s rs cols out H
  obtain ⟨t, c₀, -, P₁, H₁⟩ := foldAt S Cl (fun _ _ => True) preTrue ft pre _ s rs cols out
    (fun _ _ _ _ _ _ _ => trivial) H
  obtain ⟨t₁, k, gs₁, hd, Pb, H₂⟩ := decidedAt pre H₁
  have Pt₁ := foldJoin S Cl ft pre [b] s t rs _ cols _ _ P₁ Pb
  obtain ⟨u₀, c₂, hu, P₂, H₃⟩ := foldAt S Cl R hR ft mid _ t₁ _ _ out hs H₂
  rw [behindApp] at P₂ H₃
  have Ph := foldJoin S Cl ft (pre ++ [b]) mid s t₁ rs _ cols _ _ Pt₁ P₂
  obtain ⟨z, k', gsB, hdB, PB, -⟩ := decidedAt (pre ++ [b] ++ mid) H₃
  have Pz := foldJoin S Cl ft (pre ++ [b] ++ mid) [B] s u₀ rs _ cols _ _ Ph PB
  obtain ⟨u, cls, e, hu', hf, hz, hq⟩ := hcall _ _ _ _ hdB
  exact ⟨t, t₁, u₀, z, u, e, cls, ⟨c₀, P₁⟩, ⟨gs₁, hd⟩, ⟨_, Pt₁⟩, ⟨c₂, Ph⟩, hu, ⟨gsB, hdB⟩, ⟨_, Pz⟩,
    hu', hf, hz, hq⟩

/-- The gatherer `claimsIn`, over any list of blocks: every run that its order names is `RunIn`. -/
theorem runInOfClaimsIn {R : S → S → Prop} (hR : Pre R) (bs' : List (Block S Cl'))
    (order' : List (Nat × String)) (hr : ∀ c ∈ bs', c.RunsStep R) (u e : S) (cls : List Cl')
    (h : claimsIn bs' order' u = .ok (cls, e)) :
    R u e ∧ ∀ o ∈ order', ∃ b' run, bs'[o.1]? = some b' ∧ b'.claims.lookup o.2 = some run ∧
      RunIn R run u e cls := by
  obtain ⟨h₁, h₂⟩ := claimsTrace S Cl' R hR bs' order' u e cls hr h
  refine ⟨h₁, fun o ho => ?_⟩
  obtain ⟨b', run, n, v, cl, v', q₁, q₂, q₃, q₄, q₅, q₆⟩ := h₂ o ho
  exact ⟨b', run, q₁, q₂, n, v, cl, v', q₃, q₄, q₅, q₆⟩

section Ledger
variable {Φ Γ : Type}

/-- At `Carries`: what a trace gives of a run that was called between u and e, at a record x behind
e. -/
def RanWith : Prop :=
  ∀ (S Cl Cl' Φ Γ : Type) (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (Q : S → List Fmt.RoundView → S → List Cl' → S → S → Prop),
    (∀ F, later F F) → (∀ F G H, later F G → later G H → later F H) →
    ∀ (pre mid : List (Block S Cl)) (b B : Block S Cl) (f : S → Except String (List Cl' × S))
      (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (t t₁ u₀ z u e : S)
      (cls : List Cl'),
      TracedWith (Carries fork heard later sized) Q pre mid b B f ft s rs cols t t₁ u₀ z u e cls →
      ∀ (run : Nat → S → Except String (List Cl' × S)),
        (∀ n v cl v', run n v = .ok (cl, v') → Carries fork heard later sized v v') →
        RunIn (Carries fork heard later sized) run u e cls →
        ∀ x, Carries fork heard later sized e x →
        ∀ g F', heard t₁ = some g → fork t₁ = some F' → sized F' →
          ∃ v cl G H, RanAt fork heard later sized g F' run v cl G ∧ fork x = some H ∧ later G H ∧
            sized H ∧ heard x = some g ∧ ∀ c ∈ cl, c ∈ cls

theorem ranWith : RanWith := by
  intro S Cl Cl' Φ Γ fork heard later sized Q lr lt pre mid b B f ft s rs cols t t₁ u₀ z u e cls hT
    run hrun hin x hx g F' hg hF hsz
  have hP := carriesPre S Φ Γ fork heard later sized lr lt
  obtain ⟨n, v, cl, v', q₃, q₄, q₅, q₆⟩ := hin
  have htv := hP.trans _ _ _ (hP.trans _ _ _ hT.toGather hT.toCall) q₄
  obtain ⟨Fv, hFv, lv, sv⟩ := htv.2 F' hF hsz
  have hvv := hrun n v cl v' q₃
  obtain ⟨G, hG, -, sG⟩ := hvv.2 Fv hFv sv
  have hvx := hP.trans _ _ _ q₅ hx
  obtain ⟨H, hH, lH, sH⟩ := hvx.2 G hG sG
  exact ⟨v, cl, G, H, ⟨htv.1 g hg, ⟨Fv, hFv, lv, sv⟩, ⟨n, v', q₃, hG⟩⟩, hH, lH, sH,
    hvx.1 g (hvv.1 g (htv.1 g hg)), q₆⟩

end Ledger

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.callsWithRight
#print axioms VerifiableInference.Desc.callsWithLeft
#print axioms VerifiableInference.Desc.foldTraceWith
#print axioms VerifiableInference.Desc.ranWith
