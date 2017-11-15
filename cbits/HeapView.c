#include "Rts.h"

StgWord gtc_heap_view_closureSize(StgClosure *closure) {
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(closure));
    return closure_sizeW(closure);
}

static void
gtc_heap_view_closure_ptrs_in_large_bitmap(StgClosure *ptrs[], StgWord *nptrs, StgClosure **p, StgLargeBitmap *large_bitmap, uint32_t size )
{
    uint32_t i, j, b;
    StgWord bitmap;

    b = 0;

    for (i = 0; i < size; b++) {
        bitmap = large_bitmap->bitmap[b];
        j = stg_min(size-i, BITS_IN(W_));
        i += j;
        for (; j > 0; j--, p++) {
            if ((bitmap & 1) == 0) {
                ptrs[(*nptrs)++] = *p;
            }
            bitmap = bitmap >> 1;
        }            
    }
}

// from rts/Printer.c
char *gtc_heap_view_closure_type_names[] = {
 [INVALID_OBJECT]        = "INVALID_OBJECT",
 [CONSTR]                = "CONSTR",
 [CONSTR_1_0]            = "CONSTR_1_0",
 [CONSTR_0_1]            = "CONSTR_0_1",
 [CONSTR_2_0]            = "CONSTR_2_0",
 [CONSTR_1_1]            = "CONSTR_1_1",
 [CONSTR_0_2]            = "CONSTR_0_2",
#if defined(GHC_8_0)
 [CONSTR_STATIC]         = "CONSTR_STATIC",
 [CONSTR_NOCAF_STATIC]   = "CONSTR_NOCAF_STATIC",
#else
 [CONSTR_NOCAF]          = "CONSTR_NOCAF",
#endif
 [FUN]                   = "FUN",
 [FUN_1_0]               = "FUN_1_0",
 [FUN_0_1]               = "FUN_0_1",
 [FUN_2_0]               = "FUN_2_0",
 [FUN_1_1]               = "FUN_1_1",
 [FUN_0_2]               = "FUN_0_2",
 [FUN_STATIC]            = "FUN_STATIC",
 [THUNK]                 = "THUNK",
 [THUNK_1_0]             = "THUNK_1_0",
 [THUNK_0_1]             = "THUNK_0_1",
 [THUNK_2_0]             = "THUNK_2_0",
 [THUNK_1_1]             = "THUNK_1_1",
 [THUNK_0_2]             = "THUNK_0_2",
 [THUNK_STATIC]          = "THUNK_STATIC",
 [THUNK_SELECTOR]        = "THUNK_SELECTOR",
 [BCO]                   = "BCO",
 [AP]                    = "AP",
 [PAP]                   = "PAP",
 [AP_STACK]              = "AP_STACK",
 [IND]                   = "IND",
#if defined(GHC_8_0)
 [IND_PERM]              = "IND_PERM",
#endif
 [IND_STATIC]            = "IND_STATIC",
 [RET_BCO]               = "RET_BCO",
 [RET_SMALL]             = "RET_SMALL",
 [RET_BIG]               = "RET_BIG",
 [RET_FUN]               = "RET_FUN",
 [UPDATE_FRAME]          = "UPDATE_FRAME",
 [CATCH_FRAME]           = "CATCH_FRAME",
 [UNDERFLOW_FRAME]       = "UNDERFLOW_FRAME",
 [STOP_FRAME]            = "STOP_FRAME",
 [BLACKHOLE]             = "BLACKHOLE",
 [BLOCKING_QUEUE]        = "BLOCKING_QUEUE",
 [MVAR_CLEAN]            = "MVAR_CLEAN",
 [MVAR_DIRTY]            = "MVAR_DIRTY",
 [ARR_WORDS]             = "ARR_WORDS",
 [MUT_ARR_PTRS_CLEAN]    = "MUT_ARR_PTRS_CLEAN",
 [MUT_ARR_PTRS_DIRTY]    = "MUT_ARR_PTRS_DIRTY",
 [MUT_ARR_PTRS_FROZEN0]  = "MUT_ARR_PTRS_FROZEN0",
 [MUT_ARR_PTRS_FROZEN]   = "MUT_ARR_PTRS_FROZEN",
 [MUT_VAR_CLEAN]         = "MUT_VAR_CLEAN",
 [MUT_VAR_DIRTY]         = "MUT_VAR_DIRTY",
 [WEAK]                  = "WEAK",
 [PRIM]	                 = "PRIM",
 [MUT_PRIM]              = "MUT_PRIM",
 [TSO]                   = "TSO",
 [STACK]                 = "STACK",
 [TREC_CHUNK]            = "TREC_CHUNK",
 [ATOMICALLY_FRAME]      = "ATOMICALLY_FRAME",
 [CATCH_RETRY_FRAME]     = "CATCH_RETRY_FRAME",
 [CATCH_STM_FRAME]       = "CATCH_STM_FRAME",
 [WHITEHOLE]             = "WHITEHOLE",
 [SMALL_MUT_ARR_PTRS_CLEAN]   = "SMALL_MUT_ARR_PTRS_CLEAN",
 [SMALL_MUT_ARR_PTRS_DIRTY]   = "SMALL_MUT_ARR_PTRS_DIRTY",
 [SMALL_MUT_ARR_PTRS_FROZEN0] = "SMALL_MUT_ARR_PTRS_FROZEN0",
 [SMALL_MUT_ARR_PTRS_FROZEN]  = "SMALL_MUT_ARR_PTRS_FROZEN",
#if defined(GHC_8_2)
 [COMPACT_NFDATA]  = "COMPACT_NFDATA",
#endif
};


void gtc_heap_view_closure_ptrs_in_pap_payload(StgClosure *ptrs[], StgWord *nptrs, StgClosure *fun, StgClosure **payload, StgWord size) {
    StgWord bitmap;
    const StgFunInfoTable *fun_info;

    fun_info = get_fun_itbl(UNTAG_CLOSURE(fun));
    // ASSERT(fun_info->i.type != PAP);
    StgClosure **p = payload;

    switch (fun_info->f.fun_type) {
    case ARG_GEN:
        bitmap = BITMAP_BITS(fun_info->f.b.bitmap);
        goto small_bitmap;
    case ARG_GEN_BIG:
        gtc_heap_view_closure_ptrs_in_large_bitmap(ptrs, nptrs, payload, GET_FUN_LARGE_BITMAP(fun_info), size);
        break;
    case ARG_BCO:
        gtc_heap_view_closure_ptrs_in_large_bitmap(ptrs, nptrs, payload, BCO_BITMAP(fun), size);
        break;
    default:
        bitmap = BITMAP_BITS(stg_arg_bitmaps[fun_info->f.fun_type]);
    small_bitmap:
        while (size > 0) {
            if ((bitmap & 1) == 0) {
                ptrs[(*nptrs)++] = *p;
            }
            bitmap = bitmap >> 1;
            p++;
            size--;
        }
        break;
    }
}

StgMutArrPtrs *gtc_heap_view_closurePtrs(Capability *cap, StgClosure *closure) {
    ASSERT(LOOKS_LIKE_CLOSURE_PTR(closure));

    StgWord size = gtc_heap_view_closureSize(closure);
    StgWord nptrs = 0;
    StgWord i;

    // First collect all pointers here, with the comfortable memory bound
    // of the whole closure. Afterwards we know how many pointers are in
    // the closure and then we can allocate space on the heap and copy them
    // there
    StgClosure *ptrs[size];

    StgClosure **end;
    StgClosure **ptr;

    const StgInfoTable *info = get_itbl(closure);
    StgThunkInfoTable *thunk_info;
    StgFunInfoTable *fun_info;

    // fprintf(stderr,"closurePtrs: Reading type %s\n", gtc_heap_view_closure_type_names[info->type]);

    switch (info->type) {
        case INVALID_OBJECT:
            barf("Invalid Object");
            break;

        // No pointers
        case ARR_WORDS:
            break;

        // Default layout
        case CONSTR_1_0:
        case CONSTR_0_1:
        case CONSTR_2_0:
        case CONSTR_1_1:
        case CONSTR_0_2:
        case CONSTR:
#if defined(GHC_8_0)
        case CONSTR_STATIC:
        case CONSTR_NOCAF_STATIC:
#else
        case CONSTR_NOCAF:
#endif
        case PRIM:

        case FUN:
        case FUN_1_0:
        case FUN_0_1:
        case FUN_1_1:
        case FUN_2_0:
        case FUN_0_2:
        case FUN_STATIC:
            end = closure->payload + info->layout.payload.ptrs;
            for (ptr = closure->payload; ptr < end; ptr++) {
                ptrs[nptrs++] = *ptr;
            }
            break;

        case THUNK:
        case THUNK_1_0:
        case THUNK_0_1:
        case THUNK_1_1:
        case THUNK_2_0:
        case THUNK_0_2:
        case THUNK_STATIC:
            end = ((StgThunk *)closure)->payload + info->layout.payload.ptrs;
            for (ptr = ((StgThunk *)closure)->payload; ptr < end; ptr++) {
                ptrs[nptrs++] = *ptr;
            }
            break;

        case THUNK_SELECTOR:
            ptrs[nptrs++] = ((StgSelector *)closure)->selectee;
            break;
            
        case AP:
            ptrs[nptrs++] = ((StgAP *)closure)->fun;
            gtc_heap_view_closure_ptrs_in_pap_payload(ptrs, &nptrs,
                ((StgAP *)closure)->fun,
                ((StgAP *)closure)->payload,
                ((StgAP *)closure)->n_args);
            break;
            
        case PAP:
            ptrs[nptrs++] = ((StgPAP *)closure)->fun;
            gtc_heap_view_closure_ptrs_in_pap_payload(ptrs, &nptrs,
                ((StgPAP *)closure)->fun,
                ((StgPAP *)closure)->payload,
                ((StgPAP *)closure)->n_args);
            break;
            
        case AP_STACK:
            ptrs[nptrs++] = ((StgAP_STACK *)closure)->fun;
            for (i = 0; i < ((StgAP_STACK *)closure)->size; ++i) {
                ptrs[nptrs++] = ((StgAP_STACK *)closure)->payload[i];
            }
            break;
            
        case BCO:
            ptrs[nptrs++] = (StgClosure *)((StgBCO *)closure)->instrs;
            ptrs[nptrs++] = (StgClosure *)((StgBCO *)closure)->literals;
            ptrs[nptrs++] = (StgClosure *)((StgBCO *)closure)->ptrs;
            break;
            
        case IND:
#if defined(GHC_8_0)
        case IND_PERM:
#endif
        case IND_STATIC:
        case BLACKHOLE:
            ptrs[nptrs++] = (StgClosure *)(((StgInd *)closure)->indirectee);
            break;

        case MUT_ARR_PTRS_CLEAN:
        case MUT_ARR_PTRS_DIRTY:
        case MUT_ARR_PTRS_FROZEN:
        case MUT_ARR_PTRS_FROZEN0:
            for (i = 0; i < ((StgMutArrPtrs *)closure)->ptrs; ++i) {
                ptrs[nptrs++] = ((StgMutArrPtrs *)closure)->payload[i];
            }
            break;
        case MUT_VAR_CLEAN:
            ptrs[nptrs++] = ((StgMutVar *)closure)->var;
            break;
        case MVAR_DIRTY:
        case MVAR_CLEAN:
            ptrs[nptrs++] = (StgClosure *)((StgMVar *)closure)->head;
            ptrs[nptrs++] = (StgClosure *)((StgMVar *)closure)->tail;
            ptrs[nptrs++] = ((StgMVar *)closure)->value;
            break;

        default:
            //fprintf(stderr,"closurePtrs: Cannot handle type %s yet\n", gtc_heap_view_closure_type_names[info->type]);
            break;
    }

    size = nptrs + mutArrPtrsCardTableSize(nptrs);
    StgMutArrPtrs *arr = 
        (StgMutArrPtrs *)allocate(cap, sizeofW(StgMutArrPtrs) + size);
    TICK_ALLOC_PRIM(sizeofW(StgMutArrPtrs), nptrs, 0);
    SET_HDR(arr, &stg_MUT_ARR_PTRS_FROZEN_info, CCCS);
    arr->ptrs = nptrs;
    arr->size = size;

    for (i = 0; i<nptrs; i++) {
        arr->payload[i] = ptrs[i];
    }

    return arr;
}
