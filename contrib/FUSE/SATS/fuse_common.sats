(*
**
** An interface
** for ATS to interact with FUSE (fuse.sourceforge.net)
**
** Contributed by Zhiqian Ren (aren AT cs DOT bu DOT edu)
** Contributed by Mark Reynolds (markreyn AT cs DOT bu DOT edu)
** Contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** Start Time: September, 2010
**
*)

(* ****** ****** *)

(*
struct fuse_file_info {
	/** Open flags.	 Available in open() and release() */
	int flags;

	/** Old file handle, don't use */
	unsigned long fh_old;

	/** In case of a write operation indicates if this was caused by a
	    writepage */
	int writepage;

	/** Can be filled in by open, to use direct I/O on this file.
	    Introduced in version 2.4 */
	unsigned int direct_io : 1;

	/** Can be filled in by open, to indicate, that cached file data
	    need not be invalidated.  Introduced in version 2.4 */
	unsigned int keep_cache : 1;

	/** Indicates a flush operation.  Set in flush operation, also
	    maybe set in highlevel lock operation and lowlevel release
	    operation.	Introduced in version 2.6 */
	unsigned int flush : 1;

	/** Can be filled in by open, to indicate that the file is not
	    seekable.  Introduced in version 2.8 */
	unsigned int nonseekable : 1;

	/** Padding.  Do not use*/
	unsigned int padding : 28;

	/** File handle.  May be filled in by filesystem in open().
	    Available in all other file operations */
	uint64_t fh;

	/** Lock owner id.  Available in locking operations and flush */
	uint64_t lock_owner;
};
*)

typedef fuse_file_info_struct =
$extype_struct "ats_fuse_file_info_type" of {
  flags= uint // the original type is [int]
, writepage= int
(*
, direct_io= uint : 1
, keep_cache= uint : 1
, flush= uint : 1
, nonseekable = uint : 1
, padding= uint : 28
*)
, fh= uint64
, lock_owner= uint64
} // end of [fuse_file_info_struct]
typedef fuse_file_info = fuse_file_info_struct

(* ****** ****** *)

(* end of [fuse_common.sats] *)
