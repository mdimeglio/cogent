{- LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DisambiguateRecordFields #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{- LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RebindableSyntax #-}
{- LANGUAGE ImplicitPrelude #-}
{-# LANGUAGE RecordWildCards #-}
{- LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}

{-# OPTIONS_GHC -Wno-missing-fields #-}
{- OPTIONS_GHC -F -pgmFderive -optF-F #-}

import Foreign
import Foreign.C.String hiding (CString)
import Foreign.C.Types
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import Data.Set as S
import Prelude
import Test.QuickCheck hiding (Success)
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic

import CogentMonad hiding (return, (>>=))
import qualified CogentMonad as CogentMonad
import FFI (Ct432(..), Ct435(..), pDummyCSysState, dummyCSysState, const_unit, const_true, const_false)
import qualified FFI as FFI
import Fsop_Shallow_Desugar 
-- import WordArray
import Util

main = do quickCheck prop_fsm_init_refine
          quickCheck prop_fsm_init_nb_free_eb

run_cogent_fsm_init = do
  mnt_st <- generate gen_MountState
  fsm_st <- generate gen_FsmState
  cogent_fsm_init mnt_st fsm_st


-- infixl 1 >>=, >>

hs_fsm_init :: MountState -> FsmState -> Cogent_monad (Either ErrCode FsmState)
hs_fsm_init mount_st fsm_st = do
  nb_free_eb <- return $ nb_eb (super mount_st) - bilbyFsFirstLogEbNum
  (return $ Left eNoMem) `alternative` (return $ Right $ fsm_st { nb_free_eb })
    where (>>=)  = (CogentMonad.>>=)
          return = CogentMonad.return

r_result :: Either ErrCode FsmState -> Cogent_monad (Either ErrCode FsmState) -> Bool
r_result r1 r2 = any (fsm_init_ret_eq r1) $ toList r2
  where fsm_init_ret_eq :: Either ErrCode FsmState -> Either ErrCode FsmState -> Bool
        fsm_init_ret_eq (Left l1) (Left l2) = l1 == l2
        fsm_init_ret_eq (Right (R94 f1 f2 f3 f4)) (Right (R94 f1' f2' f3' f4')) = f1 == f1'
        fsm_init_ret_eq _ _ = False

gen_MountState :: Gen MountState
gen_MountState = arbitrary

gen_FsmState :: Gen FsmState
gen_FsmState = arbitrary

prop_fsm_init_refine = monadicIO $ forAllM gen_MountState $ \mount_st ->
                                   forAllM gen_FsmState   $ \fsm_st   -> run $ do
                                     ra <- cogent_fsm_init mount_st fsm_st
                                     rc <- return $ hs_fsm_init mount_st fsm_st
                                     r  <- return $ ra `r_result` rc
                                     release_fsm_init ra
                                     return r

prop_fsm_init_nb_free_eb = forAll gen_MountState $ \mount_st ->
                           forAll gen_FsmState   $ \fsm_st   -> 
                             nb_eb (super mount_st) >= bilbyFsFirstLogEbNum ==>
                             let rs = hs_fsm_init mount_st fsm_st
                              in all (\r -> case r of
                                              Left _  -> True
                                              Right s -> nb_free_eb s <= nb_eb (super mount_st)) rs

foreign import ccall unsafe "fsm_wrapper_pp_inferred.c ffi_fsm_init"
  c_fsm_init :: Ptr Ct432 -> IO (Ptr Ct435)

release_fsm_init :: Either ErrCode FsmState -> IO ()
release_fsm_init (Left _) = return ()
release_fsm_init (Right r) = conv_FsmState r >>= new >>= c_destroy_Ct68

foreign import ccall unsafe "fsm_wrapper_pp_inferred.c ffi_destroy_Ct68"
  c_destroy_Ct68 :: Ptr FFI.Ct68 -> IO ()

conv_ObjSuper :: ObjSuper -> IO FFI.Ct39
conv_ObjSuper (R93 {..}) = 
  return $ FFI.Ct39 { FFI.nb_eb           = fromIntegral nb_eb
                    , FFI.eb_size         = fromIntegral eb_size
                    , FFI.io_size         = fromIntegral io_size
                    , FFI.nb_reserved_gc  = fromIntegral nb_reserved_gc
                    , FFI.nb_reserved_del = fromIntegral nb_reserved_del
                    , FFI.cur_eb          = fromIntegral cur_eb
                    , FFI.cur_offs        = fromIntegral cur_offs
                    , FFI.last_inum       = fromIntegral last_inum
                    , FFI.next_sqnum      = fromIntegral next_sqnum
                    }

conv_ObjData :: ObjData -> IO FFI.Ct62
conv_ObjData (R82 {..}) = do
  p_odata <- new =<< conv_WordArray (return . fromIntegral) odata
  return $ FFI.Ct62 (fromIntegral id) p_odata

conv_ObjDel :: ObjDel -> IO FFI.Ct63
conv_ObjDel (R79 x) = return $ FFI.Ct63 $ fromIntegral x

conv_ObjDentry :: ObjDentry -> IO FFI.Ct48
conv_ObjDentry (R86 {..}) = do
  p_name <- new =<< conv_WordArray (return . fromIntegral) name
  return $ FFI.Ct48 { FFI.ino   = fromIntegral ino
                    , FFI.dtype = fromIntegral dtype
                    , FFI.nlen  = fromIntegral nlen
                    , FFI.name  = p_name
                    }

conv_Array :: (Storable t') => (t -> IO t') -> Array t -> IO (FFI.CArray t')
conv_Array f xs = do
  p_values   <- newArray =<< mapM f xs
  p_p_values <- new p_values
  return $ FFI.CArray (CInt $ fromIntegral $ length xs) p_p_values

conv_ObjDentarr :: ObjDentarr -> IO FFI.Ct64
conv_ObjDentarr (R80 {..}) = do
  p_entries <- new =<< conv_Array conv_ObjDentry entries
  return $ FFI.Ct64 { id = fromIntegral id
                    , nb_dentry = fromIntegral nb_dentry
                    , entries = p_entries
                    }

conv_ObjInode :: ObjInode -> IO FFI.Ct45
conv_ObjInode (R83 {..}) = 
  return $ FFI.Ct45 { FFI.id        = fromIntegral id
                    , FFI.size      = fromIntegral size
                    , FFI.atime_sec = fromIntegral atime_sec
                    , FFI.ctime_sec = fromIntegral ctime_sec
                    , FFI.mtime_sec = fromIntegral mtime_sec
                    , FFI.nlink     = fromIntegral nlink
                    , FFI.uid       = fromIntegral uid
                    , FFI.gid       = fromIntegral gid
                    , FFI.mode      = fromIntegral mode
                    , FFI.flags     = fromIntegral flags
                    }

conv_WordArray :: (Storable t') => (t -> IO t') -> WordArray t -> IO (FFI.CWordArray t')
conv_WordArray f xs = FFI.CWordArray (fromIntegral $ length xs) <$> (newArray =<< mapM f xs)

conv_ObjSumEntry :: ObjSumEntry -> IO (FFI.Ct10)
conv_ObjSumEntry (R84 {..}) = 
  return $ FFI.Ct10 { FFI.id    = fromIntegral id
                    , FFI.sqnum = fromIntegral sqnum
                    , FFI.len   = fromIntegral len
                    , FFI.del_flags_and_offs = fromIntegral del_flags_and_offs
                    , FFI.count = fromIntegral count
                    }

conv_ObjSummary :: ObjSummary -> IO FFI.Ct42
conv_ObjSummary (R95 {..}) = do
  p_entries <- new =<< conv_WordArray conv_ObjSumEntry entries
  return $ FFI.Ct42 { FFI.nb_sum_entry = fromIntegral nb_sum_entry
                    , FFI.entries      = p_entries
                    , FFI.sum_offs     = fromIntegral sum_offs
                    }

conv_ObjUnion :: ObjUnion -> IO FFI.Ct65
conv_ObjUnion ounion = do
  let def_data    = FFI.Ct62 {id = 0, odata = nullPtr}
      def_del     = FFI.Ct63 {id = 0}
      def_dentarr = nullPtr
      def_inode   = nullPtr
      def_pad     = const_unit
      def_summary = nullPtr
      def_super   = nullPtr
      o = FFI.Ct65 undefined def_data def_del def_dentarr def_inode def_pad def_summary def_super
  case ounion of
    TObjData    t -> conv_ObjData    t         >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjData   , FFI.tObjData    = x }
    TObjDel     t -> conv_ObjDel     t         >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjDel    , FFI.tObjDel     = x }
    TObjDentarr t -> conv_ObjDentarr t >>= new >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjDentarr, FFI.tObjDentarr = x }
    TObjInode   t -> conv_ObjInode   t >>= new >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjInode  , FFI.tObjInode   = x }
    TObjPad     t ->                                     return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjPad    , FFI.tObjPad     = const_unit }
    TObjSummary t -> conv_ObjSummary t >>= new >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjSummary, FFI.tObjSummary = x }
    TObjSuper   t -> conv_ObjSuper   t >>= new >>= \x -> return $ o { FFI.tag = FFI.Ctag_t $ fromIntegral $ fromEnum FFI.tag_ENUM_TObjSuper  , FFI.tObjSuper   = x }

conv_Obj :: Obj -> IO FFI.Ct66
conv_Obj (R90 {..}) = do
  ounion' <- conv_ObjUnion ounion
  return $ FFI.Ct66 { FFI.magic  = fromIntegral magic
                    , FFI.crc    = fromIntegral crc
                    , FFI.sqnum  = fromIntegral sqnum
                    , FFI.offs   = fromIntegral offs
                    , FFI.trans  = fromIntegral trans
                    , FFI.otype  = fromIntegral otype
                    , FFI.ounion = ounion'
                    }

conv_UbiVolInfo :: UbiVolInfo -> IO FFI.CUbiVolInfo
conv_UbiVolInfo = return

conv_UbiDevInfo :: UbiDevInfo -> IO FFI.CUbiDevInfo
conv_UbiDevInfo = return

conv_MountState :: MountState -> IO FFI.Ct72
conv_MountState (R19 {..}) = do
  p_super   <- new =<< conv_ObjSuper super
  p_obj_sup <- new =<< conv_Obj obj_sup
  p_vol     <- new =<< conv_UbiVolInfo vol
  p_dev     <- new =<< conv_UbiDevInfo dev
  return $ FFI.Ct72 { eb_recovery      = fromIntegral eb_recovery
                    , eb_recovery_offs = fromIntegral eb_recovery_offs
                    , super            = p_super
                    , obj_sup          = p_obj_sup
                    , super_offs       = fromIntegral super_offs
                    , vol              = p_vol
                    , dev              = p_dev
                    , no_summary       = FFI.Cbool_t $ CUChar $ fromIntegral $ fromEnum no_summary
                    }

conv_GimNode :: GimNode -> IO FFI.Ct18
conv_GimNode (R13 {..}) = return $ FFI.Ct18 (fromIntegral count) (fromIntegral sqnum)

-- Rbt is not refined
conv_Rbt :: (Storable k', Storable v') => (k -> IO k') -> (v -> IO v') -> Rbt k v -> IO (FFI.CRbt k' v')
conv_Rbt fk fv t = ttraverse fk =<< traverse fv t

conv_FsmState :: FsmState -> IO FFI.Ct68
conv_FsmState (R94 {..}) = do
  p_used_eb     <- new =<< conv_WordArray (return . fromIntegral) used_eb
  p_dirty_space <- new =<< conv_WordArray (return . fromIntegral) dirty_space
  p_gim         <- new =<< conv_Rbt (return . fromIntegral) conv_GimNode gim
  return $ FFI.Ct68 { nb_free_eb  = fromIntegral nb_free_eb
                    , used_eb     = p_used_eb
                    , dirty_space = p_dirty_space
                    , gim         = p_gim
                    }

mk_fsm_init_arg :: MountState -> FsmState -> IO Ct432
mk_fsm_init_arg mount_st fsm_st = do
  p_sys_st   <- pDummyCSysState
  p_mount_st <- new =<< conv_MountState mount_st
  p_fsm_st   <- new =<< conv_FsmState fsm_st
  return $ Ct432 { p1 = p_sys_st, p2 = p_mount_st, p3 = p_fsm_st }

conv_Ct433 :: FFI.Ct433 -> IO ErrCode
conv_Ct433 (FFI.Ct433 {..}) = return $ fromIntegral p1

conv_CWordArray :: (Storable t) => (t -> IO t') -> FFI.CWordArray t -> IO (WordArray t')
conv_CWordArray f (FFI.CWordArray {..}) = mapM f =<< peekArray (fromIntegral len) values

conv_Ct18 :: FFI.Ct18 -> IO GimNode
conv_Ct18 (FFI.Ct18 {..}) = return $ R13 (fromIntegral count) (fromIntegral sqnum)

conv_CRbt :: (Storable k, Storable v) => (k -> IO k') -> (v -> IO v') -> FFI.CRbt k v -> IO (Rbt k' v')
conv_CRbt fk fv t = ttraverse fk =<< traverse fv t

conv_Ct68 :: FFI.Ct68 -> IO FsmState
conv_Ct68 (FFI.Ct68 {..}) = do
  p_used_eb     <- peek used_eb     >>= conv_CWordArray (return . fromIntegral)
  p_dirty_space <- peek dirty_space >>= conv_CWordArray (return . fromIntegral)
  p_gim         <- peek gim         >>= conv_CRbt (return . fromIntegral) conv_Ct18
  return $ R94 (fromIntegral nb_free_eb) p_used_eb p_dirty_space p_gim

conv_Ct434 :: FFI.Ct434 -> IO (Either ErrCode FsmState)
conv_Ct434 (FFI.Ct434 {..}) = do
  let FFI.Ctag_t t = tag
  if | fromIntegral t == fromEnum FFI.tag_ENUM_Error   -> conv_Ct433 error >>= return . Left
     | fromIntegral t == fromEnum FFI.tag_ENUM_Success -> (conv_Ct68 =<< peek success) >>= return . Right
     | otherwise -> Prelude.error $ "Tag is " ++ show (fromIntegral t)

conv_Ct435 :: Ct435 -> IO (Either ErrCode FsmState)
conv_Ct435 (Ct435 {..}) = conv_Ct434 p2

mk_fsm_init_ret :: Ct435 -> IO (Either ErrCode FsmState)
mk_fsm_init_ret = conv_Ct435

cogent_fsm_init :: MountState -> FsmState -> IO (Either ErrCode FsmState)
cogent_fsm_init mount_st fsm_st = do
  p_arg <- new =<< mk_fsm_init_arg mount_st fsm_st
  p_ret <- c_fsm_init p_arg
  -- putStrLn $ "p_ret = " ++ show p_ret
  ret <- peek p_ret
  -- putStrLn $ "ret = " ++ show ret
  mk_fsm_init_ret ret