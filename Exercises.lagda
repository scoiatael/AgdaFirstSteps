\documentclass{scrartcl}

% current annoyance: this will be fixed
% by the next update of agda.fmt
\def\textmu{}

%include agda.fmt

%format not = "not"

\usepackage[T1]{fontenc}
% \usepackage[utf8]{inputenc} 
\usepackage[polish]{babel} 
\usepackage{listings}

\newtheorem{zadanie}{Zadanie}

\author{Wojciech Jedynak \and Piotr Polesiuk}
\title{Ćwiczenia z Agdy -- część pierwsza}

\begin{document}
\lstset{language=Haskell}

\maketitle

\section{Uwaga}

Niniejszy dokument stanowi pierwszą część zadań z Agdy. Rozwiązując
wszystkie 9 zadań można uzyskać zaliczenie jednej listy seminaryjnej.
Wkrótce pojawi się lista druga (za drugi punkt), która będzie składać
się z jednego dużego (fascynującego!) zadania.

Lista zadań jest dostępna w dwu wariantach .pdf i .lagda. Wersję
.lagda można otworzyć w edytorze tekstu i uzupełniać brakujące
fragmenty bez przepisywania wszystkiego. Rozwiązania części pierwszej
przyjmujemy do \textbf{20 stycznia 2014 roku}. Rozwiązania w postaci
uzupełnionego pliku .lagda należy wysyłać e-mailem na adres
\texttt{wjedynak@@gmail.com} lub \texttt{piotr.polesiuk@@gmail.com}. Zachęcamy także do
zadawania pytań! 

\begin{code}
module Exercises where

\end{code}

\section{Podstawy Izomorfizmu Curry'ego-Howarda}

Fałsz zdefiniowaliśmy w Agdzie jako typ pusty:

\begin{code}

data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

\end{code}

Możemy teraz wyrazić negację w standardowy sposób: jako funkcję w zbiór pusty.

\begin{code}

¬_ : Set → Set
¬ A = A → ⊥

\end{code}

\begin{zadanie}
Udowodnij, że p ⇒ ¬¬p, czyli dokończ poniższą definicję:

\begin{code}
pnnp : {A : Set} → A → ¬ ¬ A
pnnp = λ a → λ na → na a
\end{code}

Czy potrafisz udowodnić implikację w drugą stronę?

\begin{code}

nnpp : {A : Set} → ¬ ¬ A → A
nnpp = λ f → {! !}

\end{code}

Wydaje się niemożliwe, ¬ nie zachowuje swojego argumentu, a go właśnie mamy pokazać. A przynajmniej tak by się wydawało jeśli byłyby to normalne funkcje.

\end{zadanie}

\begin{zadanie}

Zdefiniuj koniunkcję jako polimorficzny typ i udowodnij reguły eliminacji oraz prawo 
przemienności tj. zdefiniuj typ A ∧ B oraz funkcje fst, snd i swap:

\begin{code}

data _∧_ (A B : Set) : Set where
  both : A → B → A ∧ B
  

fst : {A B : Set} → A ∧ B → A
fst (both x x₁) = x

snd : {A B : Set} → A ∧ B → B
snd (both x x₁) = x₁

swap : {A B : Set} → A ∧ B → B ∧ A
swap (both x x₁) = both x₁ x

\end{code}

\end{zadanie}

\begin{zadanie}

Korzystając z koniunkcji z poprzedniego zadania i alternatywy z
wykładu, sformułuj i spróbuj udowodnić prawa De~Morgana znane z logiki
klasycznej. Które z nich zachodzą w logice kostruktywnej?

\begin{code}

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B
  
M1RProof : {A B : Set} → ¬ (A ∧ B) → (¬ A) ∨ (¬ B)
M1RProof negAnd = {!!}
M1LProof : {A B : Set} → (¬ A) ∨ (¬ B) → ¬ (A ∧ B)
M1LProof (inl x) (both x₁ x₂) = x x₁
M1LProof (inr x) (both x₁ x₂) = x x₂
M2RProof : {A B : Set} → ¬ (A ∨ B) → (¬ A) ∧ (¬ B)
M2RProof negOr = {!!}
M2LProof : {A B : Set} → (¬ A) ∧ (¬ B) → ¬ (A ∨ B)
M2LProof (both x x₁) (inl x₂) = x x₂
M2LProof (both x x₁) (inr x₂) = x₁ x₂

\end{code}

Widać, że w dowodach M1R i M2R kolejny krokiem byłoby rozważenie obu konstruktorów inl i inr w zależności od potrzeby; jednak w Agdzie musimy z góry podać który z konstruktorów wybieramy, co nie pozwala dowieść praw de morgana w jedną stronę.

\end{zadanie}

\section{Liczby naturalne}

Na wykładzie zdefiniowaliśmy liczby naturalne z dodawaniem następująco:

\begin{code}

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

infix 6 _+_ 

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

\end{code}

\begin{zadanie}
Przypomnijmy definicję równości:

\begin{code}
infix 5 _≡_

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

\end{code}

Pamiętając, że wg Izomorfizmu Curry'ego-Howarda indukcja to rekursja,
udowodnij następujące własności dodawania:

\begin{code}
subst : {A : Set}{x y : A}(P : A → Set) → x ≡ y → P x → P y
subst P refl v = v
 
plus-right-zero : (n : ℕ) → n + 0 ≡ n
plus-right-zero zero = refl
plus-right-zero (suc x) = {! subst refl (plus-right-zero x) !}

plus-suc-n-m : (n m : ℕ) → suc (n + m) ≡ n + suc m
plus-suc-n-m = {!!}
\end{code}

\end{zadanie}

\begin{zadanie}
Korzystając z poprzedniego zadania, udowodnij przemienność dodawania:

\begin{code}
plus-commutative : (n m : ℕ) → n + m ≡ m + n
plus-commutative = {!!}
\end{code}

\end{zadanie}



\section{Wektory}

Przypomnijmy definicję wektorów:

\begin{code}

data Vec (A : Set) : ℕ → Set where
  []  : Vec A 0
  _∷_ : {n : ℕ} → (x : A) → (xs : Vec A n) → Vec A (suc n)

\end{code}

Zdefiniowaliśmy już m.in. konkatenację wektorów:

\begin{code}

_++_ : {A : Set} → {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
[]       ++ v2 = v2
(x ∷ v1) ++ v2 = x ∷ (v1 ++ v2)

\end{code}

\begin{zadanie}

Zaprogramuj funkcję vmap, która jest wektorowym odpowiednikiem map dla list.
Jaka powinna być długość wynikowego wektora?

\end{zadanie}

\begin{zadanie}

W Haskellu bardzo często używamy funkcji zip, która jest zdefiniowana następująco: \\
\\
zip :: [a] -> [b] -> [(a,b)] \\
zip (x:xs) (y:ys) = (x,y) : zip xs ys \\
zip \_ \_ = [] \\

Jak widać, przyjęto tutaj, że jeśli listy są różnej długości, to dłuższa lista jest ucinana.
Nie zawsze takie rozwiązanie jest satysfakcjonujące. Wymyśl taką sygnaturę dla funkcji zip na wektorach,
aby nie dopuścić (statycznie, za pomocą systemu typów) do niebezpiecznych wywołań.

\end{zadanie}

\begin{zadanie}

Zaprogramuj \textbf{wydajną} funkcję odwracającą wektor. Użyj funkcji
subst z wykładu, jeśli będziesz chciał zmusić Agdę do stosowania praw
arytmetyki.

\end{zadanie}

\begin{zadanie}

Rozważmy funkcję filter na wektorach. Jaka powinna być długość wektora wynikowego?
Długość ta zależy od zadanego predykatu i samego wektora ... Możliwe są trzy podejścia:
\begin{enumerate}
\item zwrócić listę zamiast wektora,
\item ukryć długość wektora używając typu egzystencjalnego ($\Sigma$ ℕ ($\lambda$ n → Vec A n)),
\item napisać pomocniczą funkcję obliczającą długość wynikowego wektora.
\end{enumerate}

Zaimplementuj wszystkie trzy warianty. W trzecim wariancie użyj następujących sygnatur:

\begin{code}
data Bool : Set where
  true false : Bool

filter-length : {A : Set}{n : ℕ} → (A → Bool) → Vec A n → ℕ
filter-length = {!!}

filter₃ : {A : Set}{n : ℕ} → (P : A → Bool) → (xs : Vec A n) → Vec A (filter-length P xs)
filter₃ = {!!}
\end{code}

\end{zadanie}

\end{document}
