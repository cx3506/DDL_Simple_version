theory DDL_automation
  imports DDL_inference
begin

lemma ReflexiveM_OB[simp]: "ReflexiveM OB \<longleftrightarrow> reflexive N_OBL"
  by simp

axiomatization where
  ReflexiveM_PE[simp]: "ReflexiveM PE" and
  ReflexiveM_IM[simp]: "ReflexiveM IM"

definition DDL_valid :: "bool \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>D\<^sub>D\<^sub>L")
  where "\<lfloor>P\<rfloor>\<^sub>D\<^sub>D\<^sub>L \<equiv> P"

definition derivable_fact :: "\<sigma> \<Rightarrow> bool" ("\<turnstile>\<^sub>F _" [100] 100)
  where "\<turnstile>\<^sub>F \<phi> \<equiv> \<phi> \<in> F"

lemma derivable_fact_sound:
  "\<turnstile>\<^sub>F \<phi> \<Longrightarrow> +d \<phi>"
  unfolding derivable_fact_def by (rule d_pos_fact)

lemma derivable_fact_complete:
  assumes "\<phi> \<in> F"
  shows "\<turnstile>\<^sub>F \<phi>"
  using assms unfolding derivable_fact_def by simp

lemma auto_derive_fact [simp]:
  "\<phi> \<in> F \<Longrightarrow> +d \<phi>"
  by (rule d_pos_fact)

lemma auto_derive_fact_iff [simp]:
  "\<turnstile>\<^sub>F \<phi> \<longleftrightarrow> \<phi> \<in> F"
  unfolding derivable_fact_def by simp

definition derives_obligation :: "\<sigma> \<Rightarrow> bool" ("\<turnstile>\<^sub>O\<^sub>B _" [100] 100)
  where "\<turnstile>\<^sub>O\<^sub>B \<phi> \<equiv> \<phi> \<in> F \<or> (ReflexiveM OB \<and> mpos OB R_OBL \<phi>)"

lemma derives_obl_sound:
  "\<turnstile>\<^sub>O\<^sub>B \<phi> \<Longrightarrow> +d \<phi>"
  unfolding derives_obligation_def
  by (auto intro: d_pos_fact d_pos_from_obl)

declare auto_derive_fact [intro]
declare derivable_fact_sound [intro]

lemmas ddl_intros = 
  d_pos_fact 
  derivable_fact_sound 
  derives_obl_sound

lemmas ddl_simps =
  derivable_fact_def
  derives_obligation_def
  DDL_valid_def

definition derives_permission :: "\<sigma> \<Rightarrow> bool" ("\<turnstile>\<^sub>P\<^sub>E _" [100] 100)
  where "\<turnstile>\<^sub>P\<^sub>E \<phi> \<equiv> ReflexiveM PE \<and> mpos PE R_PER \<phi>"

definition derives_prohibition :: "\<sigma> \<Rightarrow> bool" ("\<turnstile>\<^sub>I\<^sub>M _" [100] 100)
  where "\<turnstile>\<^sub>I\<^sub>M \<phi> \<equiv> ReflexiveM IM \<and> mpos IM R_IM \<phi>"

lemma derives_permission_from_rule:
  assumes "r \<in> R_PER"
      and "applicable r"
      and "head r = PE \<phi>"
      and "\<phi> \<notin> F"
  shows "\<turnstile>\<^sub>P\<^sub>E \<phi>"
proof -
  have "mpos PE R_PER \<phi>"
    using assms by (auto intro: mpos_intro)
  moreover have "ReflexiveM PE"
    by simp
  ultimately show ?thesis
    unfolding derives_permission_def by simp
qed

lemma derives_per_sound':
  assumes "\<turnstile>\<^sub>P\<^sub>E \<phi>"
  shows "mpos PE R_PER \<phi>"
  using assms unfolding derives_permission_def by simp

lemma derives_pro_sound':
  assumes "\<turnstile>\<^sub>I\<^sub>M \<phi>"
  shows "mpos IM R_IM \<phi>"
  using assms unfolding derives_prohibition_def by simp

fun derive_fact_comp :: "\<sigma> \<Rightarrow> bool" where
  "derive_fact_comp \<phi> = (\<phi> \<in> F)"

lemma derive_fact_comp_sound:
  assumes "derive_fact_comp \<phi>"
  shows "+d \<phi>"
  using assms unfolding derive_fact_comp.simps by (rule d_pos_fact)

abbreviation fact_valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>F") where
  "\<lfloor>\<phi>\<rfloor>\<^sub>F \<equiv> \<phi> \<in> F"

abbreviation DDL_derivable :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sub>D") where
  "\<lfloor>\<phi>\<rfloor>\<^sub>D \<equiv> +d \<phi>"

abbreviation DDL_obligatory :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>\<circle><_>\<rfloor>") where
  "\<lfloor>\<circle><\<phi>>\<rfloor> \<equiv> mpos OB R_OBL \<phi>"

abbreviation DDL_permitted :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>\<diamond><_>\<rfloor>") where
  "\<lfloor>\<diamond><\<phi>>\<rfloor> \<equiv> mpos PE R_PER \<phi>"

abbreviation DDL_prohibited :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>\<times><_>\<rfloor>") where
  "\<lfloor>\<times><\<phi>>\<rfloor> \<equiv> mpos IM R_IM \<phi>"

end

