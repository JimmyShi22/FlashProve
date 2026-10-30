-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/RanAtChain.lean: THE ROAD "WHO PAYS K3RanAt", FROM A CHAIN's FOLD TO ONE OF ITS
LINKS: `ranAtOfLinkAtFo` | `ranAtToSettlingAtFo` (Johnson/Desc/First/LedgerAtFo.lean) at a link that
stands in a chain. General in the record, the claims, the two readings and the chain. Definitions
and theorems with their proofs. Over Block.lean.

  `Chain.upToLink c Ls₁`, `Chain.behindLink c Ls₂`: the chain's flat list in front of, and behind,
    the link that stands behind the links Ls₁.
  `Chain.flat_at`: c.blocksInOrder = c.upToLink Ls₁ ++ (L.blocksInOrder ++ c.behindLink Ls₂).
  `Chain.upToLink_take`: so c.upToLink Ls₁ is c.blocksInOrder's first stretch of its own length.
  `linkFoldOfChain`: where the chain's fold goes on, so does the link's own, FROM THE RECORD, THE
    ROUNDS AND THE COLUMNS THAT THE FOLD OVER `upToLink` LEAVES.
  **`ranAtChainFo`**: the link's three laws (the places behind b step; the runs step; the batching
    has called the link's own gatherer) and the chain's fold's yes give the link's trace and
    `RanUpTo` at the record behind the link's claims, AND `RanAllUpTo`: the like for every run that
    the link's order names, of whichever hearing block. `ranAtChainToSettlingFo`: on to a place of
    the closing.
  `ranAtInside`: a run that, by its kind's law, is called inside a run that ran.

WHAT STANDS UNDER "THERE IS". The link's first record m and the columns c' that are left there are
values of a function: they stand with the equation `foldBlocks ft (c.upToLink Ls₁) s rs cols =
.ok (m, behindOf (c.upToLink Ls₁) rs, c')`, which has one solution at most. The link's rounds are
named: `behindOf (c.upToLink Ls₁) rs`. Of the trace's records t, t₁, u₀ and z are values of folds
(`Traced`'s own fields); u, e and cls are pinned through the letter Q (what the batching's law says
of its call) and the field `called` alone. The groups of opened columns that are handed to b and to
the batching stand under "there is" in `Traced`.

Limits. A frame's law: no error; nothing on soundness. The three laws are premises here. Which
chain a description folds is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.LedgerAtFo
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Model

variable {S Cl : Type}

/-- The chain's flat list in front of the link that stands behind the links Ls₁. -/
def Chain.upToLink (c : Chain S Cl) (Ls₁ : List (Link S Cl)) : List (Block S Cl) :=
  c.first.asBare :: c.front.map Block.asBare ++ Ls₁.flatMap Link.blocksInOrder

/-- The chain's flat list behind the link in front of the links Ls₂. -/
def Chain.behindLink (c : Chain S Cl) (Ls₂ : List (Link S Cl)) : List (Block S Cl) :=
  Ls₂.flatMap Link.blocksInOrder ++ c.back.map Block.asBare ++ [c.last.asBare]

theorem Chain.flat_at (c : Chain S Cl) (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl)
    (hl : c.links = Ls₁ ++ L :: Ls₂) :
    c.blocksInOrder = c.upToLink Ls₁ ++ (L.blocksInOrder ++ c.behindLink Ls₂) := by
  rw [Chain.flat_eq, hl]
  simp [Chain.upToLink, Chain.behindLink]

/-- So the flat list in front of a link is a first stretch of the chain's flat list, by length. -/
theorem Chain.upToLink_take (c : Chain S Cl) (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl)
    (hl : c.links = Ls₁ ++ L :: Ls₂) :
    c.blocksInOrder.take (c.upToLink Ls₁).length = c.upToLink Ls₁ := by
  rw [Chain.flat_at c Ls₁ Ls₂ L hl]
  exact List.take_left' rfl

/-- **Where the chain's fold goes on, so does the link's own**, from what the fold in front of it
leaves. -/
theorem linkFoldOfChain (c : Chain S Cl) (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl)
    (hl : c.links = Ls₁ ++ L :: Ls₂) (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn) (H : foldBlocks ft c.blocksInOrder s rs cols = .ok out) :
    ∃ m c', foldBlocks ft (c.upToLink Ls₁) s rs cols =
        .ok (m, behindOf (c.upToLink Ls₁) rs, c') ∧
      ∃ out', foldBlocks ft L.blocksInOrder m (behindOf (c.upToLink Ls₁) rs) c' = .ok out' := by
  rw [Chain.flat_at c Ls₁ Ls₂ L hl] at H
  obtain ⟨m, c', -, P₁, H₁⟩ := foldAt S Cl (fun _ _ => True) preTrue ft (c.upToLink Ls₁) _ s rs
    cols out (fun _ _ _ _ _ _ _ => trivial) H
  obtain ⟨m', c'', -, P₂, -⟩ := foldAt S Cl (fun _ _ => True) preTrue ft L.blocksInOrder _ m _ c' out
    (fun _ _ _ _ _ _ _ => trivial) H₁
  exact ⟨m, c', P₁, _, P₂⟩

/-! ## Every run that the link's order names, whichever hearing block states it -/

/-- `RanUpTo` for ALL runs of the link's order, not b's own alone: if the record t₁ holds g as heard
and a ledger F' with its sizes: g still stands at x; x holds a ledger H with its sizes, later than
F'; and EVERY run that the order names, of whichever hearing block, `RanAt` …, leaving a ledger G
with "later G H", its claims among cls. WHY: the lookup's files' law asks `K3RanAt`, at what K3's
block heard, of two runs of K3's own block and of one run ("join") of THE CALLING KIND's block, one
place behind. -/
def RanAllUpTo {Φ Γ : Type} (fork : S → Option Φ) (heard : S → Option Γ) (later : Φ → Φ → Prop)
    (sized : Φ → Prop) (L : Link S Cl) (t₁ x : S) (cls : List Cl) : Prop :=
  ∀ g F', heard t₁ = some g → fork t₁ = some F' → sized F' →
    heard x = some g ∧ ∃ H, fork x = some H ∧ later F' H ∧ sized H ∧
      ∀ o ∈ L.order, ∃ b' run v cl G, L.hear[o.1]? = some b' ∧
        b'.claims.lookup o.2 = some run ∧ RanAt fork heard later sized g F' run v cl G ∧
        later G H ∧ ∀ c ∈ cl, c ∈ cls

/-- From a trace at `Carries`, and `Carries` from e to a record x. -/
theorem ranAllUpTo {Φ Γ : Type} {fork : S → Option Φ} {heard : S → Option Γ}
    {later : Φ → Φ → Prop} {sized : Φ → Prop}
    {Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop}
    (hP : Pre (Carries fork heard later sized)) {L : Link S Cl} {h₁ : List (Block S Cl)}
    {b : Block S Cl} (hr : ∀ c ∈ L.hear, c.RunsStep (Carries fork heard later sized)) {ft : Nat}
    {s : S} {rs : List Fmt.RoundView} {cols : List OpenedColumn} {t t₁ u₀ z u e : S} {cls : List Cl}
    (hT : Traced (Carries fork heard later sized) Q L h₁ b ft s rs cols t t₁ u₀ z u e cls) (x : S)
    (hx : Carries fork heard later sized e x) :
    RanAllUpTo fork heard later sized L t₁ x cls := by
  intro g F' hg hF hsz
  have htu := hP.trans _ _ _ hT.toBatch hT.toCall
  have htx := hP.trans _ _ _ htu (hP.trans _ _ _ hT.along hx)
  obtain ⟨Hh, hH, lH, sH⟩ := htx.2 F' hF hsz
  refine ⟨htx.1 g hg, Hh, hH, lH, sH, fun o ho => ?_⟩
  obtain ⟨b', run, n, v, cl, v', q₁, q₂, q₃, q₄, q₅, q₆⟩ :=
    (claimsTrace S Cl _ hP L.hear L.order u e cls hr
      (claimsIn_of_claimsInBy L.each L.hear L.order u (cls, e) hT.called)).2 o ho
  have htv := hP.trans _ _ _ htu q₄
  obtain ⟨Fv, hFv, lv, sv⟩ := htv.2 F' hF hsz
  have hvv : Carries fork heard later sized v v' :=
    hr b' (List.mem_of_getElem? q₁) (o.2, run) (memOfLookup _ _ _ q₂) n v cl v' q₃
  obtain ⟨G, hG, -, sG⟩ := hvv.2 Fv hFv sv
  obtain ⟨H', hH', lH', -⟩ := (hP.trans _ _ _ q₅ hx).2 G hG sG
  have eH : H' = Hh := Option.some.inj (hH'.symm.trans hH)
  exact ⟨b', run, v, cl, G, q₁, q₂, ⟨htv.1 g hg, ⟨Fv, hFv, lv, sv⟩, ⟨n, v', q₃, hG⟩⟩, eH ▸ lH', q₆⟩

/-- **A run inside a run.** Where a run `outer` that `RanAt` … has, by its kind's law, called a run
`inner` between its two records, with `Carries` on both sides, `inner` too `RanAt` …, and the ledger
that it leaves is earlier than, or is, the one that `outer` leaves. FOR THE PLACES AT WHICH NO NAMED
RUN OF THE ORDER IS THE LOOKUP's SECOND OR THIRD RUN (a layers' link; the lookup on the digits):
there these claims are made inside the calling kind's own run. -/
theorem ranAtInside {Φ Γ : Type} {fork : S → Option Φ} {heard : S → Option Γ}
    {later : Φ → Φ → Prop} {sized : Φ → Prop} (lt : ∀ F G H, later F G → later G H → later F H)
    {g : Γ} {F' : Φ} {outer inner : Nat → S → Except String (List Cl × S)} {v : S} {cl : List Cl}
    {G : Φ} (h : RanAt fork heard later sized g F' outer v cl G)
    (law : ∀ n v cl v', outer n v = .ok (cl, v') → ∃ n' w cl' w', inner n' w = .ok (cl', w') ∧
      Carries fork heard later sized v w ∧ Carries fork heard later sized w w' ∧
      Carries fork heard later sized w' v' ∧ ∀ c ∈ cl', c ∈ cl) :
    ∃ w cl' G', RanAt fork heard later sized g F' inner w cl' G' ∧ later G' G ∧
      ∀ c ∈ cl', c ∈ cl := by
  obtain ⟨F, hF, lF, sF⟩ := h.later
  obtain ⟨n, v', hrun, hG⟩ := h.ran
  obtain ⟨n', w, cl', w', hin, c₁, c₂, c₃, hm⟩ := law n v cl v' hrun
  obtain ⟨Fw, hFw, lw, sw⟩ := c₁.2 F hF sF
  obtain ⟨G', hG', -, sG'⟩ := c₂.2 Fw hFw sw
  obtain ⟨G'', hG'', lG, -⟩ := c₃.2 G' hG' sG'
  have e : G'' = G := Option.some.inj (hG''.symm.trans hG)
  exact ⟨w, cl', G', ⟨c₁.1 g h.heard, ⟨Fw, hFw, lt _ _ _ lF lw, sw⟩, ⟨n', w', hin, hG'⟩⟩, e ▸ lG,
    hm⟩

/-- **The road at a link of a chain.** -/
theorem ranAtChainFo (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop) (c : Chain S Cl)
    (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl) (hl : c.links = Ls₁ ++ L :: Ls₂)
    (h₁ h₂ : List (Block S Cl)) (b : Block S Cl) (hh : L.hear = h₁ ++ b :: h₂)
    (hs : ∀ x ∈ h₂, x.Steps (CarriesFo fork heard))
    (hr : ∀ x ∈ L.hear, x.RunsStep (CarriesFo fork heard))
    (hc : CallsAt (CarriesFo fork heard) Q L.batched (claimsInBy L.each L.hear L.order))
    (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft c.blocksInOrder s rs cols = .ok out) :
    ∃ m c', foldBlocks ft (c.upToLink Ls₁) s rs cols =
        .ok (m, behindOf (c.upToLink Ls₁) rs, c') ∧
      ∃ t t₁ u₀ z u e cls,
        Traced (CarriesFo fork heard) Q L h₁ b ft m (behindOf (c.upToLink Ls₁) rs) c' t t₁ u₀ z u
          e cls ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
        RanAllUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls := by
  obtain ⟨m, c', P₁, out', P₂⟩ := linkFoldOfChain c Ls₁ Ls₂ L hl ft s rs cols out H
  obtain ⟨t, t₁, u₀, z, u, e, cls, hT, hU⟩ :=
    ranAtOfLinkAtFo S Cl fork heard Q L h₁ h₂ b hh hs hr hc ft m _ c' out' P₂
  have hP := carriesPre S Fork Forest.Heard fork heard _root_.Fo.Later OnBytes.PscRun.Sized
    _root_.Fo.Later.refl fun _ _ _ => _root_.Fo.Later.trans
  exact ⟨m, c', P₁, t, t₁, u₀, z, u, e, cls, hT, hU, ranAllUpTo hP hr hT e (hP.refl e)⟩

/-- **The like, on to the settling**: at the record in front of the decision of d, a place of the
closing. -/
theorem ranAtChainToSettlingFo (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : S → List Fmt.RoundView → S → List Cl → S → S → Prop) (c : Chain S Cl)
    (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl) (hl : c.links = Ls₁ ++ L :: Ls₂)
    (h₁ h₂ c₁ c₂ : List (Block S Cl)) (b d : Block S Cl) (hh : L.hear = h₁ ++ b :: h₂)
    (hcl : L.close = c₁ ++ d :: c₂)
    (hs : ∀ x ∈ h₂, x.Steps (CarriesFo fork heard))
    (hr : ∀ x ∈ L.hear, x.RunsStep (CarriesFo fork heard))
    (hc : CallsAt (CarriesFo fork heard) Q L.batched (claimsInBy L.each L.hear L.order))
    (ha : ∀ x ∈ L.hear, x.AfterStep (CarriesFo fork heard))
    (hs₁ : ∀ x ∈ c₁, x.Steps (CarriesFo fork heard))
    (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (H : foldBlocks ft c.blocksInOrder s rs cols = .ok out) :
    ∃ m c', foldBlocks ft (c.upToLink Ls₁) s rs cols =
        .ok (m, behindOf (c.upToLink Ls₁) rs, c') ∧
      ∃ t t₁ u₀ z u e cls w w₁,
        Traced (CarriesFo fork heard) Q L h₁ b ft m (behindOf (c.upToLink Ls₁) rs) c' t t₁ u₀ z u
          e cls ∧
        (∃ k, foldBlocks ft (L.upTo c₁) m (behindOf (c.upToLink Ls₁) rs) c' =
          .ok (w, behindOf (L.upTo c₁) (behindOf (c.upToLink Ls₁) rs), k)) ∧
        (∃ gs, d.decide w (shownAt (L.upTo c₁) d (behindOf (c.upToLink Ls₁) rs)) gs = .ok w₁) ∧
        (∃ k, foldBlocks ft (L.upTo c₁ ++ [d]) m (behindOf (c.upToLink Ls₁) rs) c' =
          .ok (w₁, behindOf (L.upTo c₁ ++ [d]) (behindOf (c.upToLink Ls₁) rs), k)) ∧
        RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ w cls := by
  obtain ⟨m, c', P₁, out', P₂⟩ := linkFoldOfChain c Ls₁ Ls₂ L hl ft s rs cols out H
  exact ⟨m, c', P₁, ranAtToSettlingAtFo S Cl fork heard Q L h₁ h₂ c₁ c₂ b d hh hcl hs hr hc ha hs₁
    ft m _ c' out' P₂⟩

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.Chain.flat_at
#print axioms VerifiableInference.Desc.Chain.upToLink_take
#print axioms VerifiableInference.Desc.linkFoldOfChain
#print axioms VerifiableInference.Desc.ranAllUpTo
#print axioms VerifiableInference.Desc.ranAtInside
#print axioms VerifiableInference.Desc.ranAtChainFo
#print axioms VerifiableInference.Desc.ranAtChainToSettlingFo
