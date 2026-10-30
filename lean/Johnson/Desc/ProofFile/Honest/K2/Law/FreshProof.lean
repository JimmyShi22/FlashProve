-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshProof.lean: the kind "the code switch" (K2): THE EQUATION
BENEATH THE STATEMENTS `SwitchFresh` (Honest/K2/Fresh.lean) AND `SwitchFreshAt`
(Honest/K2/FreshAt.lean): at the part written out and two lists of entries, FROM THE SENDER's SECOND
LAW AS A PREMISE. Statements with their proofs. The two statements themselves are proved in
Honest/K2/Law/FreshAtProof.lean, by one text.

  `fresh_after`     the sender's second law, with a function laid on what the sending shows
  `coreShows_as`    `coreShows` (Honest/K2/Law/SwitchMoves.lean) is some function of `senderShows`
                    at some data, whether the main rows' data is there or refused
  `fresh_at`        the equation, at the part written out and two lists of entries
  `seated_place`    a tool: the member that a search by place finds in a list stands at that place

Limits. The sender's law is a premise of `fresh_after` and `fresh_at`; no sender is named here.
Nothing here says what the statements would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExactProof
import Johnson.Desc.ProofFile.Honest.K2.Fresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle Block Place)
open VerifiableInference.Desc.K2.Honest (Sizes zeroG)

theorem fresh_after (Sd : Sender) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (es ks : List Ahead) (data : Nat → Nat → Nat → Cb.Gl.E)
    (seeds : List Fmt.Ext3) (asks : List (List Nat))
    (g : Option (List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E) →
      Option (List Shown))
    (h : (Prob.unif (Cs (sendingDue codes sent fresh))).map (fun c =>
        (cutAll c es, senderShows Sd codes sent fresh data seeds asks c, cutAll c ks)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs (sendingDue codes sent fresh))).map fun a =>
        (some a.1, senderShows Sd codes sent fresh data seeds asks a.2, cutAll a.2 ks)) :
    (Prob.unif (Cs (sendingDue codes sent fresh))).map (fun c =>
        (cutAll c es, g (senderShows Sd codes sent fresh data seeds asks c), cutAll c ks)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs (sendingDue codes sent fresh))).map fun a =>
        (some a.1, g (senderShows Sd codes sent fresh data seeds asks a.2), cutAll a.2 ks) := by
  have h' := congrArg (PMF.map fun t => (t.1, g t.2.1, t.2.2)) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  exact h'

theorem coreShows_as (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) (Dx : Except String (Nat → Nat → Nat → Cb.Gl.E)) :
    ∃ (g : Option (List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E) →
        Option (List Shown)) (data : Nat → Nat → Nat → Cb.Gl.E),
      ∀ c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)),
        coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks Dx c =
          g (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) data x₁.elems
            ((asks[0]?).getD []) c) := by
  cases Dx with
  | error e =>
    exact ⟨fun _ => none, fun _ _ _ => zeroG,
      fun c => coreShows_error Sd Z others k d₁ d₂ o₁ o₂ x₁ asks e c⟩
  | ok D =>
    exact ⟨afterSend Z d₁ d₂ o₁ o₂, D,
      fun c => coreShows_ok Sd Z others k d₁ d₂ o₁ o₂ x₁ asks D c⟩

variable {S Cl W₀ Rc Xi Tr X : Type}

/-- **The equation, at the part written out.** -/
theorem fresh_at (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (nm : String) (ad : Addr) (v : Option (Local W₀ Rc Xi Tr)) (es ks : List Ahead)
    (sp : CsAll ([] : List (String × Due))) (ca : CsAll p.carries)
    (m : Mid (Local W₀ Rc Xi Tr) X) (x₁ x₂ : Fmt.Drawn) (asks : List (List (List Nat)))
    (hlaw : ∀ data : Nat → Nat → Nat → Cb.Gl.E,
      (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)))).map (fun c =>
          (cutAll c es, senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD []) c,
            cutAll c ks)) =
        (Prob.unif (CsAll (es.map Ahead.named) ×
          Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars)))).map fun a =>
          (some a.1, senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD []) a.2,
            cutAll a.2 ks)) :
    (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)))).map (fun c =>
        (cutAll c es,
          (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad [(d₁, o₁), (d₂, o₂)] v
            (c, sp, ca)) [x₁, x₂] [] m).toOption.map (fun y => shownOf y.1 asks),
          cutAll c ks)) =
      (Prob.unif (CsAll (es.map Ahead.named) ×
        Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)))).map fun a =>
        (some a.1,
          (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad [(d₁, o₁), (d₂, o₂)] v
            (a.2, sp, ca)) [x₁, x₂] [] m).toOption.map (fun y => shownOf y.1 asks),
          cutAll a.2 ks) := by
  obtain ⟨g, data, hg⟩ := coreShows_as Sd p.sizes p.others p.foldVars d₁ d₂ o₁ o₂ x₁ asks
    (switchRowsAt p.sizes p.carries ca (m.st.narrow (switchWit D readers closing p) fun _ => ()) 0)
  have e : ∀ c : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars)),
      (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad [(d₁, o₁), (d₂, o₂)] v
        (c, sp, ca)) [x₁, x₂] [] m).toOption.map (fun y => shownOf y.1 asks) =
      g (senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD []) c) :=
    fun c => (lifted_shows Sd p.sizes p.others p.foldVars p.carries (fun _ => ())
      (switchWit D readers closing p) (fun _ => ()) (fun x _ => x) nm ad d₁ d₂ o₁ o₂ v c ca x₁ x₂
      m asks).trans (hg c)
  have eL : (fun c : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) =>
        (cutAll c es,
          (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad [(d₁, o₁), (d₂, o₂)] v
            (c, sp, ca)) [x₁, x₂] [] m).toOption.map (fun y => shownOf y.1 asks),
          cutAll c ks)) =
      fun c => (cutAll c es,
        g (senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD []) c),
        cutAll c ks) :=
    funext fun c => by rw [e c]
  have eR : (fun a : CsAll (es.map Ahead.named) ×
        Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)) =>
        (some a.1,
          (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad [(d₁, o₁), (d₂, o₂)] v
            (a.2, sp, ca)) [x₁, x₂] [] m).toOption.map (fun y => shownOf y.1 asks),
          cutAll a.2 ks)) =
      fun a => (some a.1,
        g (senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD []) a.2),
        cutAll a.2 ks) :=
    funext fun a => by rw [e a.2]
  exact (congrArg (fun f => PMF.map f (Prob.unif _)) eL).trans
    ((fresh_after Sd p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) es ks data x₁.elems ((asks[0]?).getD []) g
      (hlaw data)).trans (congrArg (fun f => PMF.map f (Prob.unif _)) eR).symm)

theorem seated_place {bs : List (Block S Cl)} {a : Place} {b : Block S Cl}
    (h : (bs.find? fun b => b.place == a) = some b) : b.place = a := by
  have h' := List.find?_some h
  exact eq_of_beq h'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.fresh_after
#print axioms ProofFile.Honest.K2.Law.coreShows_as
#print axioms ProofFile.Honest.K2.Law.fresh_at
#print axioms ProofFile.Honest.K2.Law.seated_place
