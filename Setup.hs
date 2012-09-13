import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.Simple.LocalBuildInfo
import Distribution.PackageDescription (PackageDescription)

main = defaultMainWithHooks $
       simpleUserHooks { postConf = postConfHook (postConf simpleUserHooks) }

postConfHook oldHook args flags descr buildInfo = case profFlag of
  Flag True -> error "This library cannot be built using profiling. Try invoking cabal with the --disable-library-profiling flag."
  _ -> oldHook args flags descr buildInfo
  where profFlag = configProfLib $ configFlags buildInfo
