-- Высказывания, связки и аксиомы

constant and'  : Prop → Prop → Prop     -- все высказывания в Lean живут в специальной вселенной Prop
                                        -- таким образом различными операциями над высказываниями являются
                                        -- просто функции над Prop

constant or'   : Prop → Prop → Prop
constant not'  : Prop → Prop
constant impl' : Prop → Prop → Prop

variables a b c : Prop

#check and' a (or' b c) -- Prop         -- поведение таких функций абсолютно аналогично населяющим вселенные Type u

constant Proof : Prop → Type            -- введем тип доказательств: для любого (a : Prop), Proof a будет содержать доказательство a

constant and_comm' : Π a b : Prop,      -- тогда аксиомы - это просто константы типа Proof от некоторого аксиоматичного высказывания
                       Proof (impl' (and' a b) (and' b a))

#check and_comm' a b -- Proof (impl' (and' a b) (and' b a)) -- "доказывает" или устанавливает аксиоматичность (a ∧ b) → (b ∧ a)


constant modus_ponens : Π a b : Prop,   -- задает правило Modes Ponens, выводящее b из (a → b) и истиности a
                          Proof (impl' a b) → Proof a → Proof b

-- Теоремы

constants p q : Prop

theorem t1 : p → q → p :=               -- для красоты записи доказательств, функции над Prop называют теоремами
  λ (hp : p), λ (hq : q), hp            -- изоморфизм Карри-Говарда говорит, что если тип обитаем, то это то же, что
                                        -- изоморфное ему высказывание истино; здесь элементарно доказывается первая аксиома
                                        -- Гильберта

theorem t1' : p → q → p :=
  assume hp : p,                        -- для красоты записи теорем вводится синтаксический сахар:
  assume hq : q,                        -- assume x : α == λ (x : α)
  hp                                    -- assume - предположим, допустим, рассмотрим

theorem t1'' : p → q → p :=
  assume hp : p,
  assume hq : q,
  show p, from hp                       -- так как в результате требуется доказать p, вводится специальный сахар
                                        -- show {type}, from {expr}

lemma l1 : p → q → p :=                 -- слово theorem можно заменить на lemma в любом месте
  assume hp : p,
  assume hq : q, 
  show p, from hp

lemma l1a (hp : p) (hq : q) : p := hp   -- аналогично функциям, аргументы можно явно поименовать

axiom hp : p                            -- еще один синтаксический сахар - слово axiom, которым можно заменять constant

theorem t2 : q → p := t1 hp             -- леммы и теоремы можно так же применять к аргументам для получения нужных значений


theorem t1_common : ∀ (p q : Prop),     -- наша оригинальная теорема работает только для конкретных p и q 
                    p → q → p :=        -- её можно записать для любых высказываний, введя квантор ∀ (\forall),
  assume p : Prop,                      -- который является полной аналогией Π для Prop
  assume q : Prop,                      -- в этом случае также требуется вводить через λ-абстракцию/assume сами высказывания
  assume hp : p,
  assume hq : q,
  show p, from hp

variables p' q' r' s' : Prop            -- как и в функциях, все можно повыносить в общие переменные

theorem t1_common_var : p' → q' → p' := -- поведение теорем и лемм в этом случае также полностью аналогично функциям
  assume hp : p',
  assume hq : q',
  show p', from hp

#check t1_common p' q' -- p' → q' → p'  -- обобщение нашей теоремы позволяет использовать её на любых высказываниях
#check t1_common r' s' -- r' → s' → r'
#check t1_common (p' → q') (s' → r') -- (p' → q') → (s' → r') → p' → q'

#check t1_common p q hp -- q → p        -- подстановка аксиомы в теорему как и прежде позволила выдать новое утверждение

theorem t3 : ∀ {p q r : Prop},          -- в теоремах также можно использовать неявные аргументы
               (q → r) → (p → q) →
               p → r :=
  assume p q r : Prop,                  -- как и в функциях, их нужно вводить, и, кстати, assume тоже поддерживает сахар
  assume h₁ : q → r,                    -- для множества переменных одного типа
  assume h₂ : p → q,                    -- красивые нижние индексы получаются через \_{символ} (например, h\_1 или h\_2)
  assume h₃ : p,
  show r, from h₁ (h₂ h₃)

#check @t3 -- ∀ {p q r : Prop}, (q → r) → (p → q) → p → r

example : p → q → p :=                  -- чтоб доказать что-то, но не засорять пространство имен, можно воспользоваться
  assume hp : p,                        -- "примером", вводимым командой example
  assume hq : q,
  show p, from hp

example (hp : p) (hq : q) : p := hp     -- примеры, как и все прочее поддерживают передачу именованных аргументов

-- Логика в стандартной библиотеке

#check a → b → a ∧ b  -- Prop           -- связки → (\r), ∧ (\and), ∨ (\or), ¬ (\not), ↔ (\iff),
#check ¬a → a ↔ false -- Prop           -- а также константы true и false уже определены в стандартной библиотеке
#check a ∨ b → b ∨ a  -- Prop

-- and

example (hp : p) (hq : q) : p ∧ q :=    -- в стандартной библиотеке определено огромное количество полезных теорем и лемм,
  and.intro hp hq                       -- которые можно и нужно активно использовать

example : p ∧ q → p :=
  assume hpq : p ∧ q,
  show p, from and.elim_left hpq

example : p ∧ q → q :=
  assume hpq : p ∧ q,
  show q, from and.elim_right hpq

#check @and.intro      -- ∀ {a b : Prop}, a → b → a ∧ b
#check @and.elim_left  -- ∀ {a b : Prop}, a ∧ b → a
#check @and.elim_right -- ∀ {a b : Prop}, a ∧ b → b

example : p ∧ q → q ∧ p :=              -- многие вещи встречаются в стандартной библиотеке по нескольку раз для удобства
  assume hpq : p ∧ q,                   -- так, and.left == and.elim_left, а and.right == and.elim_right
  show q ∧ p, from ⟨and.right hpq, and.left hpq⟩ -- and.intro можно заменить на ⟨,⟩ (\< и \>)

example : p ∧ q → q ∧ p :=
  assume hpq : p ∧ q,
  show q ∧ p, from ⟨hpq.right, hpq.left⟩-- еще немного сахара, and.left hpq можно заменить на hpq.left и т.д.

example (hpq : p ∧ q) : q ∧ p :=        -- наиболее короткая, но, imho, малопонятная запись доказательства
 ⟨hpq.right, hpq.left⟩                  -- каждый выбирает сам, но, кажется, в доказательстве теорем решает вербозность

-- or

example : p → p ∨ q :=                  -- аналогичные вещи есть для и ∨ (и кучи других вещей)
  assume hp : p,
  show p ∨ q, from or.intro_left q hp

example : q → p ∨ q :=
  assume hq : q,
  show p ∨ q, from or.intro_right p hq

example : p ∨ q → q ∨ p :=
  assume hpq : p ∨ q,
  or.elim hpq                           -- or.elim (x : a ∨ b) предлагат рассмотреть два случая: истинность а и b
    (assume hp : p,                     -- если в обоих случаях удается привести доказательство, то общее утверждение доказано
     show q ∨ p, from or.inr hp)
    (assume hq : q,                     -- or.inr и or.inl являются аналогами intro_*, но с обоими неявными аргументами
     show q ∨ p, from or.inl hq)

#check @or.intro_left  -- ∀ (a : Prop) {b : Prop}, a → a ∨ b
#check @or.intro_right -- ∀ {a : Prop} (b : Prop), b → a ∨ b
#check @or.inl         -- ∀ {a b : Prop}, a → a ∨ b
#check @or.inr         -- ∀ {a b : Prop}, b → a ∨ b

-- not

example : (p → q) → ¬q → ¬p :=          -- not играет роль обычной унарной функции типа p → false
  assume h₁ : p → q,                    -- в связи с этим в assume последнего отрицания можно писать
  assume h₂ : ¬q,                       -- assume h : p, и тогда останется доказать только false
  assume h₃ : p,
  show false, from h₂ (h₁ h₃)

example : p → ¬p → q :=                 -- false.elim позволяет вывести что угодно из лжи
  assume hp : p,
  assume hnp : ¬p,
  false.elim (hnp hp)

example : p → ¬p → q :=                 -- аналогичным поведением обладает absurd, принимающий утверждение и его отрицание,
  assume hp : p,                        -- и возвращающий что угодно
  assume hnp : ¬p,
  absurd hp hnp

#check @false.elim -- Π {c : Type u}, false → c
#check @absurd     -- Π {a : Prop} {c : Type u}, a → ¬a → c

-- equiv

