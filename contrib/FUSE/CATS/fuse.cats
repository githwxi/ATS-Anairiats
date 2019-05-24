/*
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
*/

//
// License: LGPL 3.0 (available at http://www.gnu.org/licenses/lgpl.txt)
//

/* ****** ****** */

#ifndef ATS_CONTRIB_FUSE_CATS
#define ATS_CONTRIB_FUSE_CATS

/* ****** ****** */

#include <fuse.h>

/* ****** ****** */
//
typedef
int (*fuse_getattr_t) (const char*, struct stat*) ;
typedef
int (*fuse_readlink_t) (const char*, char*, size_t) ;
typedef
int (*fuse_getdir_t)
  (const char*, fuse_dirh_t, fuse_dirfil_t) ; // Deprecated!
// end of [fuse_getdir_t]
typedef
int (*fuse_mknod_t) (const char*, mode_t, dev_t) ;
typedef
int (*fuse_mkdir_t) (const char*, mode_t) ;
typedef
int (*fuse_unlink_t) (const char*) ;
typedef
int (*fuse_rmdir_t) (const char*) ;
typedef
int (*fuse_symlink_t) (const char*, const char*) ;
typedef
int (*fuse_rename_t) (const char*, const char*) ;
typedef
int (*fuse_link_t) (const char*, const char*) ;
typedef
int (*fuse_chmod_t) (const char*, mode_t) ;
typedef
int (*fuse_chown_t) (const char*, uid_t, gid_t) ;
typedef
int (*fuse_truncate_t) (const char*, off_t) ;
typedef
int (*fuse_open_t) (const char*, struct fuse_file_info*) ;
//
typedef
int (*fuse_read_t) (
  const char*, char*, size_t, off_t, struct fuse_file_info*
) ; // end of [fuse_read_t]
typedef
int (*fuse_write_t) (
  const char*, const char*, size_t, off_t, struct fuse_file_info*
) ; // end of [fuse_write_t]
//
typedef
int (*fuse_statfs_t) (const char*, struct statvfs*) ;
typedef
int (*fuse_flush_t) (const char*, struct fuse_file_info*) ;
typedef
int (*fuse_release_t) (const char*, struct fuse_file_info*) ;
typedef
int (*fuse_fsync_t) (const char*, int, struct fuse_file_info*) ;
//
typedef
int (*fuse_getxattr_t) (const char*, const char*, char*, size_t) ;
typedef
int (*fuse_setxattr_t) (
  const char*, const char*, const char*, size_t, int
) ; // end of [fuse_setxattr_t]
//
typedef
int (*fuse_listxattr_t) (const char*, char*, size_t) ;
typedef
int (*fuse_removexattr_t) (const char*, const char*) ;
//
typedef
int (*fuse_opendir_t) (const char*, struct fuse_file_info*) ;
typedef
int (*fuse_readdir_t) (
  const char*, void*, fuse_fill_dir_t, off_t, struct fuse_file_info*
) ; // end of [fuse_readdir_t]
typedef
int (*fuse_releasedir_t) (const char*, struct fuse_file_info*) ;
typedef
int (*fuse_fsyncdir_t) (const char*, int, struct fuse_file_info*) ;
//
typedef
void* (*fuse_init_t) (struct fuse_conn_info*) ;
typedef
void (*fuse_destroy_t) (void*) ; // called on filesystem exit
//
typedef
int (*fuse_access_t) (const char*, int) ;
typedef
int (*fuse_create_t) (const char*, mode_t, struct fuse_file_info*) ;
typedef
int (*fuse_ftruncate_t) (const char*, off_t, struct fuse_file_info*) ;
typedef
int (*fuse_fgetattr_t) (const char*, struct stat*, struct fuse_file_info*) ;
typedef
int (*fuse_lock_t) (const char*, struct fuse_file_info*, int, struct flock*) ;
typedef
int (*fuse_utimens_t) (const char*, const struct timespec tv[2]) ;
typedef
int (*fuse_bmap_t) (const char *, size_t blocksize, uint64_t *idx) ;
//
typedef
int (*fuse_ioctl_t) (
  const char*, int, void*, struct fuse_file_info*, unsigned int, void*
) ; // end of [fuse_ioctl_t]
typedef
int (*fuse_poll_t) (
  const char*, struct fuse_file_info*, struct fuse_pollhandle*, unsigned int*
) ; // end of [fuse_poll_t]
//
/* ****** ****** */

typedef struct fuse ats_fuse_type ;
typedef struct fuse_file_info ats_fuse_file_info_type ;

/* ****** ****** */

#endif /* [ATS_CONTRIB_FUSE_CATS] */

/* end of [fuse.cats] */
