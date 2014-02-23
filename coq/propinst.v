Require Import typesystem.
Require Import typesystemextra.

(** Type of propositional instances *)
Definition propinst (k : obj) :=
  (* [κ] := ∀(β:★). (Π(α:κ)β) → β *)
  TFor KStar (TArr (TPi (lift 1 0 k) (TVar (S O))) (TVar O)).

Lemma propinst_cobj :
  forall k, cobj k CKind -> cobj (propinst k) CType.
Proof.
  intros k Hk. repeat constructor.
  apply cobj_lift. auto.
Qed.

Lemma propinst_jeq :
  forall k k', jeq k k' CKind -> jeq (propinst k) (propinst k') CType.
Proof.
  intros k k' Hkk'. unfold propinst.
  do 5 constructor; auto.
  apply jeq_lift. auto.
Qed.

Ltac crush_cobj :=
  match goal with
    | |- cobj (lift _ _ _) _ =>
      apply cobj_lift
    | |- cobj _ _ =>
      try repeat constructor; try auto
  end.

Ltac crush_jobj :=
  try assumption; match goal with
    | |- mxx.mE ?v -> _ => let Hmode := fresh "Hmode" in intro Hmode
    | |- mxx.mS ?v -> _ => let Hmode := fresh "Hmode" in intro Hmode
    | |- context [ Jwf (lift 1 0 ?t) ?C ] =>
      replace (Jwf (lift 1 0 t) C)
      with (jlift 1 0 (Jwf t C))
        by auto
    | |- context [ JT (lift 1 0 ?t) (lift 1 0 ?k) ] =>
      replace (JT (lift 1 0 t) (lift 1 0 k))
      with (jlift 1 0 (JT t k))
        by auto
    | |- context [ JT (lift 1 0 ?t) ?k ] =>
      replace (JT (lift 1 0 t) k)
      with (jlift 1 0 (JT t k))
        by auto
    | H : jobj ?v ?H _ |-
      jobj ?v (HCons ?H _) (jlift 1 0 _) =>
      apply jobj_shift_0
    | Hyp : jobj ?v ?H ?J, Hmode : mxx.mE ?v |- jobj ?v ?H _ =>
      pose (@jobj_extra v H J Hmode Hyp) as Hextra;
      simpl in Hextra
    | |- jobj ?v (HCons ?H ?k1) (JT (TVar ?n) ?k2) =>
      replace k2 with (lift (S n) 0 k2) by auto;
      apply JTVar; repeat constructor
    | Hyp : jobj ?v ?H (JT ?s ?k) |- jobj ?v ?H (JP _ _ (PExi ?k)) =>
      apply JPExi with (t := s)

    | |- jobj ?v ?H (JH (HCons _ _)) => apply (JHCons _ _ _ H)
    | |- jobj ?v ?H (JH HNil) => apply JHNil
    | |- jobj ?v ?H (JC _ _ _ _ (TFor _ _)) => apply JCGen
    | |- jobj ?v ?H (JC _ _ _ (TFor _ _) _) => apply JCInst
    | |- jobj ?v ?H (JT (TFor _ _) KStar) => apply JTFor
    | |- jobj ?v ?H (JT TOne KStar) => apply JTOne
    | |- jobj ?v ?H (JT (TArr _ _) KStar) => apply JTArr
    | |- jobj ?v ?H (JT (TPi _ _) KStar) => apply JTPi
    | |- jobj ?v ?H (JK _) => apply JKexi
    | |- jobj ?v ?H (JP _ _ (PExi KStar)) =>
      apply JPExi with (t := TOne)
    | |- jobj ?v ?H (Jwf _ CKind) => constructor

    | |- Happ _ _ _ => repeat constructor
    | |- cobj _ _ => crush_cobj
  end.

Lemma propinst_jobj :
  forall v H k
    (HH : jobj v HNil (Jwf H CTEnv))
    (Hk : jobj v H (JK k))
  , jobj v H (JT (propinst k) KStar).
Proof.
  intros.
  destruct (jobj_class Hk) as [Hcobj Hclassjudg].
  simpl in Hclassjudg.
  unfold propinst.
  (* TFor *)
  constructor; [ constructor; auto | ].
  (* TArr *)
  repeat constructor; repeat crush_jobj; auto.
Qed.

(* Term-level introduction and elemination forms *)
Require Import Llanguage.
Require Import Ltypesystem.

Ltac crush_jterm :=
  match goal with
    | |- jterm ?v ?H ?G (Lam _) (TArr _ _) => apply JLam
    | |- jobj _ _ _ => crush_jobj
  end.

Definition deltaG_intro := Lam (Inst (Var 0)).
Definition deltaG_elim w a  := App w (Gen a).

Lemma termgen_admissible :
  forall v H G k a t
    (Hk : jobj v H (JK k))
    (Ht : jobj v (HCons H k) (JT t KStar))
    (Hat : jterm v (HCons H k) (typesystem.lift 1 0 G) a t)
  , jterm v H G a (TFor k t).
Proof.
  intros.
  destruct (jobj_class Hk) as [Hkcobj _].
  destruct (jobj_class Ht) as [_ [Htcobj _]].
  apply (JCoer v H (HCons HNil k) (HCons H k) _ _ t);
    repeat crush_jobj.
Qed.

Definition terminst_admissible :
  forall v H G k a t s
    (Hk : jobj v H (JK k))
    (Hkwf : (mxx.mE v -> jobj v H (Jwf k CKind)))
    (Ha : jterm v H G a (TFor k t))
    (Ht : jobj v (HCons H k) (JT t KStar))
    (Hs : jobj v H (JT s k))
  , jterm v H G a (typesystem.subst s 0 t).
Proof.
  intros.
  destruct (jobj_class Hk) as [Hkcobj _].
  destruct (jobj_class Ht) as [_ [Htcobj _]].
  destruct (jobj_class Hs) as [_ [Hscobj _]].
  apply (JCoer v H HNil H G a (TFor k t) (typesystem.subst s 0 t));
    repeat crush_jobj.
  rewrite typesystem.lift_0. assumption.
Qed.

Lemma star_coherent :
  forall v H, cobj H CTEnv -> jobj v H (JK KStar).
Proof.
  intros v H HH.
  repeat crush_jobj.
Qed.

Lemma deltaG_intro_jterm :
  forall v H G k s
    (HG : cobj G CAEnv)
    (Hhwf : jobj v HNil (Jwf H CTEnv))
    (HH : jobj v HNil (JH H))
    (Hsk : jobj v H (JT s k))
  , jterm v H G deltaG_intro (propinst k).
Proof.
  intros.
  destruct (jobj_class Hsk) as [Hkcobj _].
  assert (jobj v H (JK k)) as HJk. {
    repeat crush_jobj.
    pose (jobj_extra Hmode Hsk Hhwf). simpl in e.
    assumption.
  }
  destruct (jobj_class HJk) as [Hcobj Hclassjudg]. simpl in Hclassjudg.
  assert (mxx.mE v -> jobj v H (Jwf k CKind)) as Hkwf. {
    intro Hmode.
    apply (@jobj_extra v H _ Hmode HJk Hhwf).
  }
  unfold deltaG_intro. unfold propinst.
  apply termgen_admissible; repeat crush_jobj; auto.
  repeat crush_jterm; repeat crush_jobj; auto.
  replace (TVar 0)
  with (typesystem.subst (typesystem.lift 1 0 s) 0 (TVar 1))
    by auto.
  apply JInst with (k':= typesystem.lift 1 0 k);
    repeat crush_jobj.
  apply JVar; repeat crush_jobj; auto.
  repeat constructor.
Qed.

Lemma deltaG_elim_jterm :
  forall v H G w k a t
    (HG : cobj G CAEnv)
    (HHwf : jobj v HNil (Jwf H CTEnv))
    (HH : jobj v HNil (JH H))
    (Hk : jobj v H (Jwf k CKind))
    (Hwk : jterm v H G w (propinst k))
    (Ht : jobj v H (JT t KStar))
    (Hat : jterm v (HCons H k)
                 (typesystem.lift 1 0 G) a (typesystem.lift 1 0 t))
  , jterm v H G (deltaG_elim w a) t.
Proof.
  intros.
  unfold deltaG_elim.
  destruct (jobj_class Hk) as [Hcobj Hclassjudg]. simpl in Hclassjudg.
  { unfold propinst in Hwk.
    apply JApp with (t := TPi k (typesystem.lift 1 0 t));
      repeat crush_jobj.
    - replace (TArr (TPi k (typesystem.lift 1 0 t)) t)
      with (typesystem.subst t 0
              (TArr (TPi (typesystem.lift 1 0 k) (TVar 1)) (TVar 0))).
      apply (terminst_admissible v H G KStar w); repeat crush_jobj.
      { simpl; repeat f_equal.
        - apply typesystem.subst_lift_0.
        - apply typesystem.lift_0.
      }
    - apply JGen; repeat crush_jobj.
  }
Qed.
