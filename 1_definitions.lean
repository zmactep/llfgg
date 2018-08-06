-- Константы

constant n : ℕ                -- n — челочисленная константа (\nat для написания ℕ)
constant x1 : bool            -- x1 объявлена как булева константа
constants m k : nat           -- m и k также являются константами из ℕ (мы можем писать nat вместо ℕ)
constants (x2 : bool)         -- через команду constants можно объявить и одну константу, 
                              -- если взять её объявление в скобки

constants α β : Type          -- мы также можем объявлять новые типы, например α (\alpha или \a) и β (\beta или \b)
constant f : α → β → α        -- наш контекст упорядочен, так что мы можем использовать объявленные
                              -- типы для новых объявлений
constants (a : α) (b : β)     -- мы можем делать несколько объявлений разного типа в одной строке, 
                              -- например a типа α и b типа β

constant F : Type → Type      -- мы можем объявлять функторы — стрелки над типами

-- Проверки типов

#check n         -- ℕ         -- #check возвращает тип выражения
#check f         -- α → β → α -- аналогично возвращаем тип f
#check ℕ         -- Type      -- ℕ имеет тип Type (иначе говорят, живет во вселенной Type)
#check α → β → α -- Type      -- любой стрелочный тип живет там же, где и сами типы

#check Type        -- Type 1  -- Type имеет тип Type 1 (живет во вслеленной Type 1)
#check Type 0      -- Type 1  -- Type — это алиас для Type 0
#check Type → Type -- Type 1  -- аналогично строке 22, стрелка из Type в Type живет в Type 1
#check Prop        -- Type    -- Prop — вселенная, где живут высказывания, сама она живет в Type

-- Применение

#check f a         -- β → α   -- мы можем проверить тип прмиенения функции f к аргументу a
#check f a b       -- α       -- применять можно сразу к нескольким аргументам, как в λ-исчислении
#check n + 42      -- ℕ       -- операторы - это тоже функции (+ определен в стандартной библиотеке)
#check F α         -- Type    -- функторы применяются к типам аналогично функциям
#check prod α β    -- Type    -- в стандартной библиотеке определено произведение типов
#check α × β       -- Type    -- prod == × (\x)
#check sum α β     -- Type    -- в стандартной библиотеке определена сумма типов
#check α ⊕ β       -- Type    -- sum == ⊕ (\o+)

#check (a,b)       -- α × β   -- тип пары значений α и β — произведение типов α и β
                              -- (,) можно читать как функцию, применяемую к a и b

-- Вселенные

universe u                    -- аналогично константам можно ввести произвольную вселенную u
constant γ : Type u           -- γ (\gamma or \g) в такой записи населяет вселенную Type u

-- Абстракция

#check fun x : α, x         -- α → α     -- мы можем использовать λ-абстракцию, 
                                         -- рассматривая fun как лямбду, а запятую как точку
#check λ x : α, x           -- α → α     -- fun == λ (\lambda или \fun)

#check λ x : α, λ y : β, x  -- α → β → α -- классическая вложенная λ-абстракция
#check λ (x : α) (y : β), x -- α → β → α -- синтаксический сахар для вложенной абстракции
#check λ (x y : α), x       -- α → α → α -- синтаксический сахар для вложенной абстракции 
                                         -- с одинаковыми типами аргументов
#check λ (f : α → β → γ)
         (g : α → β)
         (x : α), f x (g x) -- ...       -- сложный пример абстракции

#check (λ x : α, x) a       -- α         -- пример сочетания абстракции и апликации в одном примере

-- Редукция

#reduce (λ x : α, x) a       -- a        -- упрощает выражение до β-NF (нормальной формы)
#reduce (λ x : α, b) (f a b) -- b        -- упрощает выражение до β-NF

#reduce tt                   -- tt       -- tt - это true для типа bool из стандартной библиотеки
#reduce ff                   -- ff       -- ff - это false для типа bool из стандартной библиотеки
#reduce x1 ∨ tt              -- tt       -- любое булевское значение или (\or для ∨) true - это true
#reduce x1 ∧ ff              -- ff       -- любое булевское значение и (\and для ∧) false - это false

#reduce n + 0                -- n        -- любое натуральное число плюс ноль дает себя же
#reduce 0 + n                -- 0 + n    -- а ноль плюс число не дает, почему, поймем позже
#reduce 40 + 2               -- 42       -- мы можем делать арифметические вычисления над числами
#reduce (λ x : nat, x + 5) 3 -- 8        -- и комбинировать их с λ-исчислением

-- Определения

def foo : ℕ := 5                         -- определение константной ℕ функции foo с телом 5

def bar : (ℕ → ℕ) → ℕ :=                 -- определение функции bar с типом возвращаемого значения (ℕ → ℕ) → ℕ
  λ f : ℕ → ℕ, f 0                       -- и телом λ f, f 0 (тип f можно опустить, он будет выведен)

def bar' := λ f : ℕ → ℕ, f 0             -- в таком случае тип функции также будет выведен

def double (x : ℕ) : ℕ := x + x          -- определение функции, принимающей один аргумент (x : ℕ)
                                         -- и удваивающей его

def double' : ℕ → ℕ := λ x : ℕ , x + x   -- та же функция в форме без явного именования аргумента

def sqrsum (x : ℕ) (y : ℕ) : ℕ :=        -- определение функции, принимающей два аргумента типа ℕ
  x * x + y * y                          -- и возвращающей сумму их квадратов

def sqrsum' (x y : ℕ) : ℕ :=             -- синтаксический сахар для записи аргументов одного типа
  x * x + y * y

def compose (α β γ : Type)               -- определение функции композиции, абстрактной по типам функций
            (f : β → γ)                  -- определяется каждая из двух функций, подходящих по типу,
            (g : α → β) : α → γ :=       -- и как их композировать на произвольном аргументе
  λ x : α, f (g x)

def curry (α β γ : Type)                 -- функции можно не определять, написав вместо их значений sorry
          (f : α × β → γ) : α → β → γ :=
  sorry                                  -- реальное значение будет λ (x : α) (y : β), f (x, y)

-- Локальное определение

#reduce let y := (a, b) in (y, y) -- ... -- локальное связывание y со значением (a, b)

def t(x : ℕ) : ℕ :=                      -- локальное связывание y внутри функции
  let y := x + x - 2 in y

#reduce let x := t 4, y := 2 in x + y    -- локальное связывание двух переменных: x и y

def flet :=                              -- локальное связывание имени a с типом ℕ и его
  let a := ℕ in λ x : a, x               -- дальнейшее использование в абстракции
#check flet                     -- ℕ → ℕ -- тип функции при этом может быть выведен автоматически

-- Печать

#print "hello"                           -- командой print можно напечатать любую строку
#print double                            -- а еще тело любой функции можно напечатать

-- Переменные

variable α1 : Type                       -- часто используемые объявления в именах функций можно заводить отдельно
variables α2 α3 : Type                   -- аналогично можно заводить сразу по несколько переменных

def f_compose (f : α2 → α3)              -- объявленные переменные могут использоваться в функции
              (g : α1 → α2) : α1 → α3 := -- (сравните с функцией compose на 97 строке, где они объявлены по месту)
  λ x : α1, f (g x)

#check compose                           -- типы обеих функций выглядят одинаково
#check f_compose

-- Секции

section my                               -- чтоб не засорять общее пространство имен можно ввести именованную (my) секцию

  variable α : Type                      -- объявленные тут переменные будут видны только внутри секции
  variable list : Type → Type
  
  def cons (a : α)                       -- аналогично и с функциями
           (tail : list α) : list α :=
    sorry

   section your                          -- секции могут быть вложенными
   
     variable β : Type
     def nil : list β := sorry           -- при этом все переменные внешний секций также будут доступны

   end your

end my

#check cons                              -- объявленные в секции функции доступны извне её

-- Пространства имен

namespace my                             -- чтоб не засорять пространство имен функций вводят namespaces

  def foo' : ℕ := 5                      -- функция внтури namespace может быть использована
  def bar' : ℕ := foo + 1                -- любой другой функцией внутри того же namespace

  namespace your                         -- пространства имен также как и секции могут быть вложенными

    def quz : ℕ := foo'                  -- элементы родительского пространства могут использоваться

  end your

end my

#reduce my.your.quz                      -- для доступа из вне требуется указать полное имя

namespace my                             -- закрытое пространство имен может быть переоткрыто
                                         -- в том числе в другом файле
  def qux : ℕ := bar' * 2

end my

open my                                  -- с помощью команды open можно поднять все определения в текущий scope
#reduce foo' + your.quz                  -- и использовать содержимое по короткому имени