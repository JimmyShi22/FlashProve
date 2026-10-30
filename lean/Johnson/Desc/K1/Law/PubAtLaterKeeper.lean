-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/PubAtLaterKeeper.lean: THE THREE
PUBLIC ITEMS OF THE TABLE's OWN LAYER (ledger m, freeAbove m, unheard) OVER A YES OF K1's TWO SORTS
OF LATER BLOCK: each item's Bool answers behind the yes as it answered in front. Statements with
their proofs.

OBJECT. The blocks: commitAtS (Johnson/Desc/K1/AtS.lean), so laterAt (Johnson/Desc/K1/Places.lean:
a link's digits), and the reads' place's joined block k1Reads (Johnson/IMR/K1Seat.lean: the sending of the
reads with the quiet step behind it). The Bools: ledgerB, freeAboveB n, unheardB
(Johnson/Desc/First/FillKeeper.lean), and through them pubAll D base
(Johnson/Desc/First/PubAll.lean) at these three items.
USER. The field pub of FillL (KeepAtLater.lean) at St := YesOf B,
where pub is pubAll D base (mgAll_pub, Johnson/Desc/Sound/MgAll.lean): pub_keeper_later is that
field's share at the three items; the Bool in front is had from the promise in front.
LETTERS. D, base, m, the public part: any. B: a block with KeepsKeeper B; two members are shown.

Why it holds. ledgerB and freeAboveB read the open ledger's slots alone (ns, next, vp, mf, gotF): a
commitment leaves them (commitAtS_slots, Johnson/Desc/K1/KeepsSlots.lean). unheardB reads
S.out.reply: a commitment writes st, book, roots, rowsOwed and the open link's L and F. The quiet
step writes the open link's tl (and t) alone.

Main names:
  KeeperAlike s s'     the three Bools answer at s' as at s · KeeperAlike.trans
  keeperAlike_of_same  from: the same ledger and the same S.out
  keeperAlike_of_slots from: both ledgers open, the same slots (PscRun.SlotsSame), the same S.out
  out_putLink · out_putFork
  keeperAlike_commitAtS  **a yes of commitAtS**, on any rounds
  QuietK q · quietK_layers | _head | _att · quietK_blockAt · quietK_readsQuietAt · quietK_k1Quiet
                       a yes of the quiet step leaves the ledger and S.out
  keeperAlike_k1Reads  **a yes of the reads' place's block**, on any rounds
  KeepsKeeper B        a yes of B, on any rounds, leaves the three Bools
  keepsKeeper_commitAtS · keepsKeeper_laterAt · keepsKeeper_k1Reads: the two sorts are members
  pubAll_keeper        at the three items pubAll D base is the table's own layer's half
  pub_ledger_later · pub_freeAbove_later · pub_unheard_later: **an item each**: an equation
  pub_keeper_later     the three in the form of FillL.pub: true in front, so true behind

IS IT EMPTY HERE? No premise but the block's own yes. That such a block ever says yes is not shown
here. Whether an item is true in front is not said: unheard is false once the reply is heard.
What is not claimed. Who makes the three items. Anything on the other public items. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ReadsStep
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.First.StateLedger
import Johnson.Desc.First.PubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Pub ledgerB freeAboveB unheardB keeperItem pubKeeper PubData
  pubAll)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {Cl Pp : Type}

/-- The three Bools of the table's own layer answer at s' as at s. -/
structure KeeperAlike (s s' : S) : Prop where
  ledger : ledgerB s' = ledgerB s
  freeAbove : ∀ n, freeAboveB n s' = freeAboveB n s
  unheard : unheardB s' = unheardB s

theorem KeeperAlike.trans {s s₁ s' : S} (h : KeeperAlike s s₁) (h' : KeeperAlike s₁ s') :
    KeeperAlike s s' :=
  ⟨h'.ledger.trans h.ledger, fun n => (h'.freeAbove n).trans (h.freeAbove n),
    h'.unheard.trans h.unheard⟩

/-- The same ledger and the same walk's result: the three answer alike. -/
theorem keeperAlike_of_same {s s' : S} (hf : s'.fork? = s.fork?) (ho : s'.out = s.out) :
    KeeperAlike s s' := by
  refine ⟨?_, fun n => ?_, ?_⟩
  · unfold ledgerB
    rw [hf]
  · unfold freeAboveB
    rw [hf]
  · unfold unheardB
    rw [ho]

/-- Both ledgers open, with the same slots, and the same walk's result: the three answer alike. -/
theorem keeperAlike_of_slots {s s' : S} {F F' : Fork} (hF : s.fork? = some F)
    (hF' : s'.fork? = some F') (e : PscRun.SlotsSame F F') (ho : s'.out = s.out) :
    KeeperAlike s s' := by
  refine ⟨?_, fun n => ?_, ?_⟩
  · unfold ledgerB
    rw [hF, hF']
    show (F'.vp.size == F'.ns && F'.mf.size == F'.ns && F'.gotF.size == F'.ns) =
      (F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns)
    rw [e.vp, e.mf, e.gotF, e.ns]
  · unfold freeAboveB
    rw [hF, hF']
    show (((List.range (F'.ns - F'.next)).all fun j => !F'.gotF.getD (F'.next + j) true) &&
        F'.ns == n) =
      (((List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true) && F.ns == n)
    rw [e.gotF, e.ns, e.next]
  · unfold unheardB
    rw [ho]

theorem out_putLink (s : S) (L : LinkCtx) : (s.putLink L).out = s.out := by
  unfold S.putLink
  split <;> first | rfl | (split <;> rfl)

theorem out_putFork (s : S) (F : Fork) : (s.putFork F).out = s.out := by
  unfold S.putFork
  split <;> first | rfl | (split <;> rfl)

/-- **A yes of commitAtS leaves the three Bools.** -/
theorem keeperAlike_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    KeeperAlike s s' := by
  obtain ⟨L, F, tl, y, _, hF, _, rfl, e⟩ := commitAtS_slots h
  have h1 : ((laid s y.w).putLink y.L).fork? = some F := by
    rw [First.S.fork_putLink, First.S.fork_of_here s (laid s y.w) rfl]
    exact hF
  refine keeperAlike_of_slots hF (First.S.fork_putFork _ F y.F h1) e ?_
  rw [out_putFork, out_putLink]
  rfl

/-- A yes of q leaves the open ledger and the walk's result. -/
def QuietK (q : Block S Unit) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → s'.fork? = s.fork? ∧ s'.out = s.out

theorem quietK_layers (P : K8.ReadsQuiet.PG) : QuietK (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  exact ⟨First.S.fork_lay s a _ ha rfl, rfl⟩

theorem quietK_head (P : K8.ReadsQuiet.PH) : QuietK (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, _, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  exact ⟨First.S.fork_head s a _ ha rfl rfl, rfl⟩

theorem quietK_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietK q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  exact ⟨First.S.fork_att s a _ ha rfl, rfl⟩

theorem quietK_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietK q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact quietK_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact quietK_head _
    · cases h

theorem quietK_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat)
    (q : Block S Unit) (h : ProofFile.readsQuietAt G l X piece = some q) : QuietK q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact quietK_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact quietK_blockAt h
    · rw [if_neg h2] at h
      cases h

/-- Where no block could be made the refuser stands, which never says yes. -/
theorem quietK_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : QuietK (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact quietK_readsQuietAt l X _ q hq

/-- **A yes of the reads' place's block leaves the three Bools.** -/
theorem keeperAlike_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s rs gs = .ok s') : KeeperAlike s s' := by
  have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
      (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
      (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
      (k1Quiet G l X).decide s₁
        (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  obtain ⟨e1, e2⟩ := quietK_k1Quiet G l X _ _ _ _ h2
  exact (keeperAlike_commitAtS (Cl := Unit) (parLater G.first (gpOf Z) l pr 1) l 1 reads s s₁ _ _
    h1).trans (keeperAlike_of_same e1 e2)

/-- A yes of B, on any rounds, leaves the three Bools. -/
def KeepsKeeper (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, B.decide s rs gs = .ok s' → KeeperAlike s s'

theorem keepsKeeper_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    KeepsKeeper (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs h => keeperAlike_commitAtS P link moment arrays s s' rs gs h

/-- The first member: a segment's later moment at the plan's numbers (a link's digits). -/
theorem keepsKeeper_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    KeepsKeeper (laterAt q gp link piece moment arrays : Block S Cl) :=
  keepsKeeper_commitAtS _ _ _ _

/-- The second member: the reads' place's joined block. -/
theorem keepsKeeper_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : KeepsKeeper (k1Reads Z G l X pr reads) :=
  fun s s' rs gs h => keeperAlike_k1Reads Z G l X pr reads s s' rs gs h

/-- At the three items the composed function is the table's own layer's half. -/
theorem pubAll_keeper (D : PubData) (base : Pub → Pp × S → Bool) (q : Pub)
    (hq : keeperItem q = true) (a : Pp × S) : pubAll D base q a = pubKeeper D.nsOf base q a := by
  cases q with
  | ledger m => rfl
  | freeAbove m => rfl
  | unheard => rfl
  | _ => simp [keeperItem] at hq

section
variable {B : Block S Cl} (hB : KeepsKeeper B) (D : PubData) (base : Pub → Pp × S → Bool)
include hB

/-- **ledger m** over the block's own yes. -/
theorem pub_ledger_later (m : Nat) (x x' : Pp × S) (h : YesOf B x x') :
    pubAll D base (.ledger m) x' = pubAll D base (.ledger m) x := by
  obtain ⟨_, rs, gs, _, hy⟩ := h
  exact (hB _ _ _ _ hy).ledger

/-- **freeAbove m** over the block's own yes. -/
theorem pub_freeAbove_later (m : Nat) (x x' : Pp × S) (h : YesOf B x x') :
    pubAll D base (.freeAbove m) x' = pubAll D base (.freeAbove m) x := by
  obtain ⟨_, rs, gs, _, hy⟩ := h
  have e : (fun n => freeAboveB n x'.2) = fun n => freeAboveB n x.2 :=
    funext (hB _ _ _ _ hy).freeAbove
  show (D.nsOf m).any (fun n => freeAboveB n x'.2) = (D.nsOf m).any fun n => freeAboveB n x.2
  rw [e]

/-- **unheard** over the block's own yes. -/
theorem pub_unheard_later (x x' : Pp × S) (h : YesOf B x x') :
    pubAll D base .unheard x' = pubAll D base .unheard x := by
  obtain ⟨_, rs, gs, _, hy⟩ := h
  exact (hB _ _ _ _ hy).unheard

/-- **The three in the form of FillL.pub**: true in front of the block's own yes, so true behind. -/
theorem pub_keeper_later (q : Pub) (hq : keeperItem q = true) (x x' : Pp × S) (h : YesOf B x x')
    (h0 : pubAll D base q x = true) : pubAll D base q x' = true := by
  cases q with
  | ledger m => rw [pub_ledger_later hB D base m x x' h]; exact h0
  | freeAbove m => rw [pub_freeAbove_later hB D base m x x' h]; exact h0
  | unheard => rw [pub_unheard_later hB D base x x' h]; exact h0
  | _ => simp [keeperItem] at hq

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.keeperAlike_commitAtS
#print axioms VerifiableInference.Desc.K1.keeperAlike_k1Reads
#print axioms VerifiableInference.Desc.K1.keepsKeeper_laterAt
#print axioms VerifiableInference.Desc.K1.keepsKeeper_k1Reads
#print axioms VerifiableInference.Desc.K1.pubAll_keeper
#print axioms VerifiableInference.Desc.K1.pub_ledger_later
#print axioms VerifiableInference.Desc.K1.pub_freeAbove_later
