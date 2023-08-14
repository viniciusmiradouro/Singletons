{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Singletons () where
import Data.Kind (Type)

------------------------------------------------------
----------------- 1.1 Phantom Types  -----------------
------------------------------------------------------

{--
A Phantom paramater in a dependent function is a  parameter that is
not used in the resulting type constructors. A Phantom type in a
type given to a phantom parameter. e.g. a is a phantom type in the
following datatype:
--}

data Foo :: a -> Type where
  Mkfoo :: Foo a

{--
Their use is to add compile time constraint to functions.
e.g. the following function can only take Foo Int values
and can only return Foo String values.
--}

transFoo :: Foo Int -> Foo String
transFoo _ = Mkfoo

{--
Of course, we can create our own datatypes and restrict the
phantom parameter to their domains, e.g.
--}

data DoorState :: Type where
  Opened :: DoorState
  Closed :: DoorState
  Locked :: DoorState
  deriving (Show, Eq)

data Door :: DoorState -> Type where
  UnsafeMkDoor :: {doorMaterial :: String} -> Door s

{--
One thing to note is that Door is a type family. But type family in the sense of
set family. That is, Door s is a bunch of types that are indexed by another type.
In a very informal way, it can be thought of a type of types. In this case, the
type that indexes it is DoorState, giving us a Type Family with 3 types: Door 'Opened,
Door 'Locked and Door 'Closed.

Having the DataKinds extension activated, which reflects our type constructors to the type level,
we can define the following doors encoding their state in their types.
--}


d1 :: Door 'Opened
d1 = UnsafeMkDoor "Birch"

d2 :: Door 'Locked
d2 = UnsafeMkDoor "Iron"

{--
Having the TypeApplications extension activated makes this even more convenient
allowing us to dispense with signatures, which is good if they aren't top level.
--}

d3 = UnsafeMkDoor @'Opened "Birch"
d4 = UnsafeMkDoor @'Locked "Irons"

{--
Now, what if we want to write a function to get the state of a door? That is simply
not possible in haskell due to type erasure. That is, types only exist at compile time
and nothing about them is known at runtime. How can we bridge that gap? Singletons.
--}

---------------------------------------------------
----------------- 1.1 Singletons  -----------------
---------------------------------------------------

{--
A Singleton is a type inhabited by exactly one value. Well, if you see where this is going
there is an bijection between the type and it's inhabitant, allowing us to talk about one of
them while talking about the other. Consider the following:
--}

data Bar :: Type where
  MkBar :: Bar

{--
By construction, Bar is a singleton as the only inhabitant it has is MkBar. Therefore, we can
weakely identify them and make a sort of brige between the Type level and the Value Level. In
this way, when the Type Bar gets erased, the value MkBar can still represent it runtime.

But how can we construct singletons en masse to reflect our types to values? Singleton generators.
(Sorry, I've come up with this name right now. You probably won't find it in a google search).

A singleton generator is a dependent injection having in it's image only singletons. Consider the
following example:
--}

data SDoorState :: DoorState -> Type where
  SOpened :: SDoorState 'Opened
  SClosed :: SDoorState 'Closed
  SLocked :: SDoorState 'Locked

{--
SDoorState associates for every DoorState a single singleton. Now it's constructor can represent
at runtime the type associated to functions. Think of of like this: Being s a DoorState,

s (Erased at runtime) <~> SDoorState s (Erased at runtime) <~> Ss (Available at runtime)

where (<~>) represents the isomorphism relation. So, given Ss, we have all the information need to
talk about s as if it were a runtime value. Also, note that we can talk about Ss as if it was a Type.

Being given a way to refer to types at runtime, we can define functions such as
--}

closeDoor :: Door 'Opened -> Door 'Closed
closeDoor (UnsafeMkDoor m) = UnsafeMkDoor m

lockDoor :: Door 'Closed -> Door 'Locked
lockDoor (UnsafeMkDoor m) = UnsafeMkDoor m

lockAnyDoor :: SDoorState s -> Door s -> Door 'Locked
lockAnyDoor = \case
    SOpened -> lockDoor . closeDoor
    SClosed -> lockDoor
    SLocked -> id

{-
lockAnyDoor takes the singleton related to the door type as argument. And it is guaranteed that they
match by the function signature. Now, we can operate with a value related to state of the door at
runtime. But what about our door state function? Now it's easy to write. Here it is:
-}

doorStatus :: SDoorState s -> Door s -> DoorState
doorStatus SOpened _ = Opened
doorStatus SClosed _ = Closed
doorStatus SLocked _ = Locked

---------------------------------------------------
----------------- 1.4 Reflection  -----------------
---------------------------------------------------

{-
The mechanism behind what allowed us to write those functions is one called reflection.
One way to put is that we are exploiting the isomorphism mentioned above in the direction
that associates a type to a value. One thing to consider is that, given a singleton constructor
we can recover the associated constructor of the base type in the following way
-}

fromSDoorState :: SDoorState s -> DoorState
fromSDoorState SOpened = Opened
fromSDoorState SClosed = Closed
fromSDoorState SLocked = Locked

{-
And, since the door is not even important to the doorStatus function, we can define a function
that abstracts the door and the pattern matching away.
-}

doorStatus' :: SDoorState s -> Door s -> DoorState
doorStatus' s _ = fromSDoorState s

-----------------------------------------------
----------------- ??????????? -----------------
-----------------------------------------------

class SingDSI s where
  sng :: SDoorState s

instance SingDSI 'Opened where
  sng = SOpened

instance SingDSI 'Closed where
  sng = SClosed

instance SingDSI 'Locked where
  sng = SLocked

-----------------------------------------------
----------------- Exercises 1 -----------------
-----------------------------------------------

unlockDoor' :: Door 'Locked -> Door 'Closed
unlockDoor' (UnsafeMkDoor m) = UnsafeMkDoor m

unlockDoor :: Integer -> Door 'Locked -> Maybe (Door 'Closed)
unlockDoor p d = if odd p then Just $ unlockDoor' d else Nothing

openDoor :: Door 'Closed -> Door 'Opened
openDoor (UnsafeMkDoor m) = UnsafeMkDoor m

openAnyDoor' :: SDoorState s -> Door s -> Door 'Opened
openAnyDoor' = \case
  SOpened -> id
  SClosed -> openDoor
  SLocked -> openDoor . unlockDoor'

openAnyDoor :: SingDSI s => Integer -> Door s -> Maybe (Door 'Opened)
openAnyDoor p d = if odd p then Just $ openAnyDoor' sng d else Nothing
