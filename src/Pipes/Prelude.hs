{-| General purpose utilities

    The names in this module clash heavily with the Haskell Prelude, so I
    recommend the following import scheme:

> import Pipes
> import qualified Pipes.Prelude as P  -- or use any other qualifier you prefer

    Note that 'String'-based 'IO' is inefficient.  The 'String'-based utilities
    in this module exist only for simple demonstrations without incurring a
    dependency on the @text@ package.

    Also, 'stdinLn' and 'stdoutLn' remove and add newlines, respectively.  This
    behavior is intended to simplify examples.  The upcoming 'ByteString' and
    'Text' utilities for @pipes@ will preserve newlines.
-}

{-# LANGUAGE RankNTypes #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Pipes.Prelude (
    -- * Producers
    -- $producers
    stdinLn,
    readLn,
    fromHandle,
    replicateM,

    -- * Consumers
    -- $consumers
    stdoutLn,
    print,
    toHandle,

    -- * Pipes
    -- $pipes
    map,
    mapM,
    mapFoldable,
    filter,
    filterM,
    take,
    takeWhile,
    drop,
    dropWhile,
    concat,
    elemIndices,
    findIndices,
    scan,
    scanM,
    chain,
    read,
    show,

    -- * Folds
    -- $folds
    fold,
    foldM,
    all,
    any,
    and,
    or,
    elem,
    notElem,
    find,
    findIndex,
    head,
    index,
    last,
    length,
    maximum,
    minimum,
    null,
    sum,
    product,
    toList,
    toListM,

    -- * Zips
    zip,
    zipWith,

    -- * Utilities
    tee,
    generalize
    ) where

import Control.Exception (throwIO, try)
import Control.Monad (liftM, replicateM_, when, unless, join)
import Control.Monad.Trans.State.Strict (get, put)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Void (absurd)
import Foreign.C.Error (Errno(Errno), ePIPE)
import qualified GHC.IO.Exception as G
import Pipes
import Pipes.Core
import Pipes.Core.Steppable
import Pipes.Internal
import Pipes.Lift (evalStateP)
import qualified System.IO as IO
import qualified Prelude
import Prelude hiding (
    all,
    and,
    any,
    concat,
    drop,
    dropWhile,
    elem,
    filter,
    head,
    last,
    length,
    map,
    mapM,
    maximum,
    minimum,
    notElem,
    null,
    or,
    print,
    product,
    read,
    readLn,
    show,
    sum,
    take,
    takeWhile,
    zip,
    zipWith )

{- $producers
    Use 'for' loops to iterate over 'Producer's whenever you want to perform the
    same action for every element:

> -- Echo all lines from standard input to standard output
> runEffect $ for P.stdinLn $ \str -> do
>     lift $ putStrLn str

    ... or more concisely:

>>> runEffect $ for P.stdinLn (lift . putStrLn)
Test<Enter>
Test
ABC<Enter>
ABC
...

-}

{-| Read 'String's from 'IO.stdin' using 'getLine'

    Terminates on end of input
-}
stdinLn :: (MonadIO m) => Producer' String m ()
stdinLn = fromHandle IO.stdin
{-# INLINABLE stdinLn #-}

-- | 'read' values from 'IO.stdin', ignoring failed parses
readLn :: (MonadIO m) => (Read a) => Producer' a m ()
readLn = stdinLn >-> read
{-# INLINABLE readLn #-}

{-| Read 'String's from a 'IO.Handle' using 'IO.hGetLine'

    Terminates on end of input
-}
fromHandle :: (MonadIO m) => IO.Handle -> Producer' String m ()
fromHandle h = go
  where
    go = do
        eof <- liftIO $ IO.hIsEOF h
        unless eof $ do
            str <- liftIO $ IO.hGetLine h
            yield str
            go
{-# INLINABLE fromHandle #-}

-- | Repeat a monadic action a fixed number of times, 'yield'ing each result
replicateM :: (Monad m) => Int -> m a -> Producer a m ()
replicateM n m = lift m >~ take n
{-# INLINABLE replicateM #-}

{- $consumers
    Feed a 'Consumer' the same value repeatedly using ('>~'):

>>> runEffect $ lift getLine >~ P.stdoutLn
Test<Enter>
Test
ABC<Enter>
ABC
...

-}

{-| Write 'String's to 'IO.stdout' using 'putStrLn'

    Unlike 'toHandle', 'stdoutLn' gracefully terminates on a broken output pipe
-}
stdoutLn :: (MonadIO m) => Consumer' String m ()
stdoutLn = go
  where
    go = do
        str <- await
        x   <- liftIO $ try (putStrLn str)
        case x of
           Left (G.IOError { G.ioe_type  = G.ResourceVanished
                           , G.ioe_errno = Just ioe })
                | Errno ioe == ePIPE
                    -> return ()
           Left  e  -> liftIO (throwIO e)
           Right () -> go
{-# INLINABLE stdoutLn #-}

-- | 'print' values to 'IO.stdout'
print :: (MonadIO m, Show a) => Consumer' a m r
print = for cat (liftIO . Prelude.print)
{-# INLINABLE print #-}

-- | Write 'String's to a 'IO.Handle' using 'IO.hPutStrLn'
toHandle :: (MonadIO m) => IO.Handle -> Consumer' String m r
toHandle handle = for cat (liftIO . IO.hPutStrLn handle)
{-# INLINABLE toHandle #-}

{- $pipes
    Use ('>->') to connect 'Producer's, 'Pipe's, and 'Consumer's:

>>> runEffect $ P.stdinLn >-> P.takeWhile (/= "quit") >-> P.stdoutLn
Test<Enter>
Test
ABC<Enter>
ABC
quit<Enter>
>>>

-}

-- | Apply a function to all values flowing downstream
map :: (Monad m) => (a -> b) -> Pipe a b m r
map f = for cat (yield . f)
{-# INLINABLE map #-}

-- | Apply a monadic function to all values flowing downstream
mapM :: (Monad m) => (a -> m b) -> Pipe a b m r
mapM f = for cat $ \a -> do
    b <- lift (f a)
    yield b
{-# INLINABLE mapM #-}

{- | Apply a function to all values flowing downstream, and
     forward each element of the result.
-}
mapFoldable :: (Monad m, Foldable t) => (a -> t b) -> Pipe a b m r
mapFoldable f = for cat (each . f)
{-# INLINABLE mapFoldable #-}

-- | @(filter predicate)@ only forwards values that satisfy the predicate.
filter :: (Monad m) => (a -> Bool) -> Pipe a a m r
filter predicate = for cat $ \a -> when (predicate a) (yield a)
{-# INLINABLE filter #-}

{-| @(filterM predicate)@ only forwards values that satisfy the monadic
    predicate
-}
filterM :: (Monad m) => (a -> m Bool) -> Pipe a a m r
filterM predicate = for cat $ \a -> do
    b <- lift (predicate a)
    when b (yield a)
{-# INLINABLE filterM #-}

-- | @(take n)@ only allows @n@ values to pass through
take :: (Monad m) => Int -> Pipe a a m ()
take n = replicateM_ n $ do
    a <- await
    yield a
{-# INLINABLE take #-}

{-| @(takeWhile p)@ allows values to pass downstream so long as they satisfy
    the predicate @p@.
-}
takeWhile :: (Monad m) => (a -> Bool) -> Pipe a a m ()
takeWhile predicate = go
  where
    go = do
        a <- await
        if (predicate a)
            then do
                yield a
                go
            else return ()
{-# INLINABLE takeWhile #-}

-- | @(drop n)@ discards @n@ values going downstream
drop :: (Monad m) => Int -> Pipe a a m r
drop n = do
    replicateM_ n await
    cat
{-# INLINABLE drop #-}

{-| @(dropWhile p)@ discards values going downstream until one violates the
    predicate @p@.
-}
dropWhile :: (Monad m) => (a -> Bool) -> Pipe a a m r
dropWhile predicate = go
  where
    go = do
        a <- await
        if (predicate a)
            then go
            else do
                yield a
                cat
{-# INLINABLE dropWhile #-}

-- | Flatten all 'Foldable' elements flowing downstream
concat :: (Monad m, Foldable f) => Pipe (f a) a m r
concat = for cat each
{-# INLINABLE concat #-}

-- | Outputs the indices of all elements that match the given element
elemIndices :: (Monad m, Eq a) => a -> Pipe a Int m r
elemIndices a = findIndices (a ==)
{-# INLINABLE elemIndices #-}

-- | Outputs the indices of all elements that satisfied the predicate
findIndices :: (Monad m) => (a -> Bool) -> Pipe a Int m r
findIndices predicate = loop 0
  where
    loop n = do
        a <- await
        when (predicate a) (yield n)
        loop $! n + 1
{-# INLINABLE findIndices #-}

-- | Strict left scan
scan :: (Monad m) => (x -> a -> x) -> x -> (x -> b) -> Pipe a b m r
scan step begin done = loop begin
  where
    loop x = do
        yield (done x)
        a <- await
        let x' = step x a
        loop $! x'
{-# INLINABLE scan #-}

-- | Strict, monadic left scan
scanM :: (Monad m) => (x -> a -> m x) -> m x -> (x -> m b) -> Pipe a b m r
scanM step begin done = do
    x <- lift begin
    loop x
  where
    loop x = do
        b <- lift (done x)
        yield b
        a  <- await
        x' <- lift (step x a)
        loop $! x'
{-# INLINABLE scanM #-}

-- | Apply an action to all values flowing downstream
chain :: (Monad m) => (a -> m ()) -> Pipe a a m r
chain f = for cat $ \a -> do
    lift (f a)
    yield a
{-# INLINABLE chain #-}

-- | Parse 'Read'able values, only forwarding the value if the parse succeeds
read :: (Monad m, Read a) => Pipe String a m r
read = for cat $ \str -> case (reads str) of
    [(a, "")] -> yield a
    _         -> return ()
{-# INLINABLE read #-}

-- | Convert 'Show'able values to 'String's
show :: (Monad m, Show a) => Pipe a String m r
show = map Prelude.show
{-# INLINABLE show #-}

{- $folds
    Use these to fold the output of a 'Producer'.  Many of these folds will stop
    drawing elements if they can compute their result early, like 'any':

>>> P.any null P.stdinLn
Test<Enter>
ABC<Enter>
<Enter>
True
>>>

-}

-- | Strict fold of the elements of a 'Producer'
fold :: (Monad m) => (x -> a -> x) -> x -> (x -> b) -> Producer a m () -> m b
fold step begin done p = unProxy p request' respond' lift' pure' begin
  where
    request' v _  _ = absurd v
    respond' a fu x = fu () $! step x a
    lift'      m  x = m >>= \f -> f x
    pure'    _    x = return (done x)
{-# INLINABLE fold #-}

-- | Strict, monadic fold of the elements of a 'Producer'
foldM
    :: (Monad m)
    => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m () -> m b
foldM step begin done p = do
    x0 <- begin
    unProxy p request' respond' lift' pure' x0
      where
        request' v _  _ = absurd v
        respond' a fu x = do
            x' <- step x a
            fu () $! x'
        lift'      m  x = m >>= \f -> f x
        pure'    _    x = done x
{-# INLINABLE foldM #-}

{-| @(all predicate p)@ determines whether all the elements of @p@ satisfy the
    predicate.
-}
all :: (Monad m) => (a -> Bool) -> Producer a m () -> m Bool
all predicate p = null $ for p $ \a -> when (not $ predicate a) (yield a)
{-# INLINABLE all #-}

{-| @(any predicate p)@ determines whether any element of @p@ satisfies the
    predicate.
-}
any :: (Monad m) => (a -> Bool) -> Producer a m () -> m Bool
any predicate p = liftM not $ null $ for p $ \a -> when (predicate a) (yield a)
{-# INLINABLE any #-}

-- | Determines whether all elements are 'True'
and :: (Monad m) => Producer Bool m () -> m Bool
and = all id
{-# INLINABLE and #-}

-- | Determines whether any element is 'True'
or :: (Monad m) => Producer Bool m () -> m Bool
or = any id
{-# INLINABLE or #-}

{-| @(elem a p)@ returns 'True' if @p@ has an element equal to @a@, 'False'
    otherwise
-}
elem :: (Monad m, Eq a) => a -> Producer a m () -> m Bool
elem a = any (a ==)
{-# INLINABLE elem #-}

{-| @(notElem a)@ returns 'False' if @p@ has an element equal to @a@, 'True'
    otherwise
-}
notElem :: (Monad m, Eq a) => a -> Producer a m () -> m Bool
notElem a = all (a /=)
{-# INLINABLE notElem #-}

-- | Find the first element of a 'Producer' that satisfies the predicate
find :: (Monad m) => (a -> Bool) -> Producer a m () -> m (Maybe a)
find predicate p = head $ for p  $ \a -> when (predicate a) (yield a)
{-# INLINABLE find #-}

{-| Find the index of the first element of a 'Producer' that satisfies the
    predicate
-}
findIndex :: (Monad m) => (a -> Bool) -> Producer a m () -> m (Maybe Int)
findIndex predicate p = head (p >-> findIndices predicate)
{-# INLINABLE findIndex #-}

-- | Retrieve the first element from a 'Producer'
head :: (Monad m) => Producer a m () -> m (Maybe a)
head p = unProxy p request' respond' lift' pure'
  where
    request' v _ = absurd v
    respond' a _ = return (Just a)
    lift'      m = join m
    pure'    _   = return Nothing
{-# INLINABLE head #-}

-- | Index into a 'Producer'
index :: (Monad m) => Int -> Producer a m () -> m (Maybe a)
index n p = head (p >-> drop n)
{-# INLINABLE index #-}

-- | Retrieve the last element from a 'Producer'
last :: (Monad m) => Producer a m () -> m (Maybe a)
last p = unProxy p request' respond' lift' pure' Nothing
  where
    request' v _  _ = absurd v
    respond' a fu _ = fu () (Just a)
    lift'      m  r = m >>= \f -> f r
    pure'    _    r = return r
{-# INLINABLE last #-}

-- | Count the number of elements in a 'Producer'
length :: (Monad m) => Producer a m () -> m Int
length = fold (\n _ -> n + 1) 0 id
{-# INLINABLE length #-}

-- | Find the maximum element of a 'Producer'
maximum :: (Monad m, Ord a) => Producer a m () -> m (Maybe a)
maximum = fold step Nothing id
  where
    step x a = Just $ case x of
        Nothing -> a
        Just a' -> max a a'
{-# INLINABLE maximum #-}

-- | Find the minimum element of a 'Producer'
minimum :: (Monad m, Ord a) => Producer a m () -> m (Maybe a)
minimum = fold step Nothing id
  where
    step x a = Just $ case x of
        Nothing -> a
        Just a' -> min a a'
{-# INLINABLE minimum #-}

-- | Determine if a 'Producer' is empty
null :: (Monad m) => Producer a m () -> m Bool
null p = do
    x <- head p
    return $ case x of
        Nothing -> True
        Just _  -> False
{-# INLINABLE null #-}

-- | Compute the sum of the elements of a 'Producer'
sum :: (Monad m, Num a) => Producer a m () -> m a
sum = fold (+) 0 id
{-# INLINABLE sum #-}

-- | Compute the product of the elements of a 'Producer'
product :: (Monad m, Num a) => Producer a m () -> m a
product = fold (*) 1 id
{-# INLINABLE product #-}

-- | Convert a pure 'Producer' into a list
toList :: Producer a Identity () -> [a]
toList p = unProxy p request' respond' lift' pure'
  where
    request' v _  = absurd v
    respond' a fu = a : fu ()
    lift'      m  = runIdentity m
    pure'    _    = []
{-# INLINABLE toList #-}

{-| Convert an effectful 'Producer' into a list

    Note: 'toListM' is not an idiomatic use of @pipes@, but I provide it for
    simple testing purposes.  Idiomatic @pipes@ style consumes the elements
    immediately as they are generated instead of loading all elements into
    memory.
-}
toListM :: (Monad m) => Producer a m () -> m [a]
toListM p = unProxy p request' respond' lift' pure'
  where
    request' v _  = absurd v
    respond' a fu = do
        as <- fu ()
        return (a:as)
    lift'      m  = join m
    pure'    _    = return []
{-# INLINABLE toListM #-}

-- | Zip two 'Producer's
zip :: (Monad m)
    => (Producer   a     m r)
    -> (Producer      b  m r)
    -> (Producer' (a, b) m r)
zip = zipWith (,)
{-# INLINABLE zip #-}

-- | Zip two 'Producer's using the provided combining function
zipWith :: (Monad m)
    => (a -> b -> c)
    -> (Producer  a m r)
    -> (Producer  b m r)
    -> (Producer' c m r)
zipWith f pa pb = fromProxySteppable $ zipWithSteppable f (toProxySteppable pa) (toProxySteppable pb)


-- | Zip two steppable 'Producer's using the provided combining function
zipWithSteppable :: (Monad m)
    => (a -> b -> c)
    -> (ProducerSteppable  a m r)
    -> (ProducerSteppable  b m r)
    -> (ProducerSteppable' c m r)
zipWithSteppable f = go
  where
    go p1 p2 = do
        e1 <- lift $ next p1
        case e1 of
            Left r         -> return r
            Right (a, p1') -> do
                e2 <- lift $ next p2
                case e2 of
                    Left r         -> return r
                    Right (b, p2') -> do
                        respondSteppable (f a b)
                        go p1' p2'
{-# INLINABLE zipWith #-}

{-| Transform a 'Consumer' to a 'Pipe' that reforwards all values further
    downstream
-}
tee :: (Monad m) => Consumer a m r -> Pipe a a m r
tee p = evalStateP Nothing $ do
    r <- up >\\ (hoist lift p //> dn)
    ma <- lift get
    case ma of
        Nothing -> return ()
        Just a  -> yield a
    return r
  where
    up () = do
        ma <- lift get
        case ma of
            Nothing -> return ()
            Just a  -> yield a
        a <- await
        lift $ put (Just a)
        return a
    dn v = absurd v
{-# INLINABLE tee #-}

{-| Transform a unidirectional 'Pipe' to a bidirectional 'Proxy'

> generalize (f >-> g) = generalize f >+> generalize g
>
> generalize cat = pull
-}
generalize :: (Monad m) => Pipe a b m r -> x -> Proxy x a x b m r
generalize p x0 = evalStateP x0 $ up >\\ hoist lift p //> dn
  where
    up () = do
        x <- lift get
        request x
    dn a = do
        x <- respond a
        lift $ put x
{-# INLINABLE generalize #-}
