-- Существование

example : ∃ x : ℕ, x > 0 :=                     -- с места в карьер докажем существование (\exists для ∃) натурального числа 
  have h : 1 > 0, from nat.zero_lt_succ 0,      -- больше 0 предъявим 1, который больше нуля по великой лемме zero_lt_one
  show ∃ x : ℕ, x > 0, from exists.intro 1 h    -- с помощью exists.intro построим из h искомое утверждение

#check (⟨1, zero_lt_one⟩ : ∃ x : ℕ, x > 0)      -- альтернативный синтаксис для exists.intro a b — ⟨a, b⟩

#check @exists.intro -- ∀ {α : Type u} {p : α → Prop} (w : α), p w → Exists p
                                                -- эта конструкция получает некоторый Exists p благодаря одному примеру, 
                                                -- на котором p выполняется
                                                
variable g : ℕ → ℕ → ℕ                          -- в записе exists.intro присутствует неявный аргумент {p : α → Prop},
variable hg : g 0 0 = 0                         -- который может принимать разные значения в зависимости от контекста

set_option pp.implicit true                     -- показ неявных аргументов при печати

theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩        -- p = λ (x : ℕ), g x x = x
#print gex1

theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩        -- p = λ (x : ℕ), g x 0 = x
#print gex2

theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩        -- p = λ (x : ℕ), g 0 0 = x
#print gex3

theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩        -- p = λ (x : ℕ), g x x = 0
#print gex4

#check @Exists -- Π {α : Type u}, (α → Prop) → Prop
                                                -- тип самого Exists понятен: из некоторого предиката в утверждение о существовании
                                                -- значения, делающего предикат истиным
                                                -- exists.intro в этом случае является просто конструктором типа Exists

example (x y z : ℕ)                             -- рассмотрим еще один пример
        (hxy : x < y)                           -- два условия устанавливают, что между x, y и z есть порядок: x < y < z
        (hyz : y < z) : 
        ∃ w : ℕ, x < w ∧ w < z :=               -- доказываем, что есть такой w, что он между y и z
  have x < y ∧ y < z, from and.intro hxy hyz,   -- такой w есть – это сам y, что мы показываем, соединяя конъюнкцией два исходных условия
  show ∃ w : ℕ, x < w ∧ w < z,                  -- получаем результат путем введения exists.intro
    from exists.intro y this

example (x y z : ℕ)                             -- вспомним синтаксический сахар для and.intro и exists.intro
        (hxy : x < y)                           
        (hyz : y < z) : 
        ∃ w : ℕ, x < w ∧ w < z := 
  have x < y ∧ y < z, from ⟨hxy, hyz⟩,          -- треугольные скобки заменяют and
  show ∃ w : ℕ, x < w ∧ w < z, from ⟨y, this⟩   -- треугольные скобки заменяют exists.intro (и это не просто так :) )
                                                -- при этом this = ⟨hxy, hyz⟩, а значит можем еще сильнее укоротить
                                                -- про не просто так. ∃ x : α, p x - это сахар для Σ x : α, p x :)
                                                -- то есть существование - это просто зависимая пара из элемента и предиката

example (x y z : ℕ)                             
        (hxy : x < y)                           
        (hyz : y < z) : 
        ∃ w : ℕ, x < w ∧ w < z := 
  show ∃ w : ℕ, x < w ∧ w < z,                  -- show можно убрать, оставив только тело from
    from ⟨y, ⟨hxy, hyz⟩⟩                        -- скобки ассоциативны, и их можно сократить

example (x y z : ℕ)                             -- вот и все доказательство
        (hxy : x < y)                           
        (hyz : y < z) : 
        ∃ w : ℕ, x < w ∧ w < z := 
  ⟨y, hxy, hyz⟩

-- Разбор существования

universe u
variable α : Type u
variables p q : α → Prop

example (h : ∃ x : α, p x ∧ q x) :              -- докажем следующее утверждение
          ∃ y : α, q y ∧ p y :=
  exists.elim h                                 -- exists.elim позволяет разобрать нашу зависимую пару на два элемента,
    (assume w : α,                              -- которые можно затем удобно использовать
     assume hw : p w ∧ q w,
     show ∃ y : α, q y ∧ p y, from exists.intro w ⟨hw.right, hw.left⟩)

#check @exists.elim -- ∀ {a : Type u} {p : α → Prop} {b : Prop}
                    --   (∃ x : α, p x) → (∀ a : α, p a → b) → b
                    --                       |      |
                    --                       |      +-- второй элемент пары
                    --                       +-- первый элемент пары

example (h : ∃ x : α, p x ∧ q x) :              -- альтернативным методом является применение pattern matching
          ∃ y : α, q y ∧ p y :=                 -- любое утверждение о существовании можно смэтчить с парой
  match h with ⟨w, hw⟩ :=
    exists.intro w ⟨hw.right, hw.left⟩          -- здесь можно было написать ⟨w, hw.right, hw.left⟩
  end

-- общий синтаксис match:
-- match {expr} with {pattern} :=
--   {operations}
-- end

example (h : ∃ x : α, p x ∧ q x) :              -- при pattern matching можно сразу разобрать конъюнкцию
          ∃ y : α, q y ∧ p y :=
  match h with ⟨w, hwl, hwr⟩ :=
    ⟨w, hwr, hwl⟩
  end

example (h : ∃ x : α, p x ∧ q x) :              -- также pattern matching доступен при локальном связывании
          ∃ y : α, q y ∧ p y :=
  let ⟨w, hwl, hwr⟩ := h in ⟨w, hwr, hwl⟩

-- Пример теоремы

def is_even (n : ℕ) : Prop :=
  ∃ b : ℕ, n = 2 * b

theorem even_plus_even {a b : ℕ}                -- рассмотрим два четных натуральных числа
                       (h₁ : is_even a)         -- это означает, что у нас есть доказательства их четности
                       (h₂ : is_even b) :
                         is_even (a + b) :=     -- докажем четность их суммы
  exists.elim h₁                                -- разберем доказательство четности первого числа
    (assume w₁  : ℕ,                            -- есть такое w₁, что a = 2 * w₁
     assume hw₁ : a = 2 * w₁,
     exists.elim h₂                             -- аналогично разберем доказательство четности второго числа
       (assume w₂  : ℕ,                         -- есть такое w₂, что b = 2 * w₂
        assume hw₂ : b = 2 * w₂,
        exists.intro (w₁ + w₂)                  -- покажем, что существует такое (w₁ + w₂), что a + b = 2 * (w₁ + w₂)
          (calc
            a + b = 2 * w₁ + 2 * w₂ : by rw [hw₁, hw₂]
            ...   = 2 * (w₁ + w₂)   : by rw mul_add)
       ))

theorem even_plus_even' {a b : ℕ}               -- докажем то же, через pattern matching
                        (h₁ : is_even a)         
                        (h₂ : is_even b) :
                          is_even (a + b) :=
  match h₁, h₂ with                             -- вычисления выше значительно сокращаются
    ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ := 
      exists.intro  (w₁ + w₂)                   -- сократить можно и эту часть, переписав calc как by rw [hw₁, hw₂, mul_add]
        (calc
          a + b = 2 * w₁ + 2 * w₂ : by rw [hw₁, hw₂]
          ...   = 2 * (w₁ + w₂)   : by rw mul_add)
  end