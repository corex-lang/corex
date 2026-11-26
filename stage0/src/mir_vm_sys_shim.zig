//! Oracle Runtime Host Syscall Shims for `MirVm` (`STD-02`)
//!
//! Dispatches `core.sys` `extern "C"` OS calls inside `MirVm` exclusively when `is_oracle_runtime_mode`
//! is enabled (`diff_oracle` Tiers 1 & 2), keeping compile-time `comptime` evaluation 100% hermetic (`E0503`).
//!
//! All buffer reads and writes marshal through `MirVm.readScalarBytes` and `MirVm.writeScalarBytes` so
//! `init_mask` bits, virtual pointer bounds, and `stdout`/`stderr` capture channels remain bit-exact.

const std = @import("std");
const builtin = @import("builtin");
const mem_foundation = @import("mem_foundation.zig");
const mir = @import("mir.zig");
const mir_vm = @import("mir_vm.zig");

const Span = mem_foundation.Span;
const MirValueId = mem_foundation.MirValueId;
const TypeId = mem_foundation.TypeId;
const MirVm = mir_vm.MirVm;
const VmEvalError = mir_vm.VmEvalError;
const RegSlot = mir_vm.RegSlot;
const SymbolicPtr = mir_vm.SymbolicPtr;
const ComptimeAllocId = mir_vm.ComptimeAllocId;
const VmCallableEntry = mir_vm.VmCallableEntry;

// ---------------------------------------- TYPES ----------------------------------------

// --------------------- Host Handle Types ----------------------

/// Opaque dispatch tag resolved in $O(1)$ from `core.sys` `@link(name: "…")` symbol names.
const ShimOp = enum(u8) {
    rt_get_argc,
    rt_get_argv,
    // Windows `kernel32` / `ntdll` / `advapi32`:
    win_get_last_error,
    win_set_last_error,
    win_get_std_handle,
    win_create_file_w,
    win_nt_create_file,
    win_rtl_nt_status_to_dos_error,
    win_read_file,
    win_write_file,
    win_flush_file_buffers,
    win_close_handle,
    win_set_file_pointer_ex,
    win_set_end_of_file,
    win_get_file_info_by_handle,
    win_get_file_info_by_handle_ex,
    win_set_file_info_by_handle,
    win_get_file_attributes_w,
    win_set_file_attributes_w,
    win_get_file_attributes_ex_w,
    win_get_final_path_name_w,
    win_get_full_path_name_w,
    win_move_file_ex_w,
    win_replace_file_w,
    win_delete_file_w,
    win_create_directory_w,
    win_remove_directory_w,
    win_create_hard_link_w,
    win_device_io_control,
    win_find_first_file_ex_w,
    win_find_next_file_w,
    win_find_close,
    win_create_file_mapping_w,
    win_map_view_of_file,
    win_unmap_view_of_file,
    win_lock_file_ex,
    win_unlock_file_ex,
    win_read_directory_changes_w,
    win_create_event_w,
    win_wait_for_single_object,
    win_get_overlapped_result,
    win_cancel_io_ex,
    win_get_console_mode,
    win_get_file_type,
    win_query_performance_counter,
    win_query_performance_frequency,
    win_get_system_time_precise,
    win_sleep,
    win_get_command_line_w,
    win_get_environment_strings_w,
    win_free_environment_strings_w,
    win_get_environment_variable_w,
    win_set_environment_variable_w,
    win_expand_environment_strings_w,
    win_get_current_directory_w,
    win_set_current_directory_w,
    win_get_module_file_name_w,
    win_get_temp_path_w,
    win_get_module_handle_w,
    win_get_proc_address,
    win_get_current_process_id,
    win_create_pipe,
    win_set_handle_information,
    win_get_handle_information,
    win_search_path_w,
    win_init_proc_thread_attr_list,
    win_update_proc_thread_attr,
    win_delete_proc_thread_attr_list,
    win_create_process_w,
    win_get_exit_code_process,
    win_terminate_process,
    win_exit_process,
    win_reg_open_key_ex_w,
    win_reg_query_value_ex_w,
    win_reg_close_key,
    // POSIX (`linux` & `macos`):
    posix_errno_location,
    posix_openat,
    posix_read,
    posix_write,
    posix_pread,
    posix_pwrite,
    posix_readv,
    posix_writev,
    posix_lseek,
    posix_ftruncate,
    posix_fchmod,
    posix_fsync,
    posix_fdatasync,
    posix_fcntl,
    posix_close,
    posix_renameat,
    posix_unlinkat,
    posix_mkdirat,
    posix_linkat,
    posix_symlinkat,
    posix_readlinkat,
    posix_realpath,
    posix_getcwd,
    posix_chdir,
    posix_clonefileat,
    posix_fcopyfile,
    posix_copy_file_range,
    posix_mmap,
    posix_munmap,
    posix_flock,
    posix_ioctl,
    posix_inotify_init1,
    posix_inotify_add_watch,
    posix_inotify_rm_watch,
    posix_kqueue,
    posix_kevent64,
    posix_poll,
    posix_isatty,
    posix_stat,
    posix_fstat,
    posix_lstat,
    posix_fstatat,
    posix_getdirentries64,
    posix_clock_gettime,
    posix_clock_gettime_nsec_np,
    posix_mach_continuous_time,
    posix_mach_timebase_info,
    posix_nanosleep,
    posix_dlsym,
    posix_getenv,
    posix_setenv,
    posix_unsetenv,
    posix_ns_get_environ,
    posix_ns_get_executable_path,
    posix_getpid,
    posix_pipe,
    posix_pipe2,
    posix_spawn_fa_init,
    posix_spawn_fa_destroy,
    posix_spawn_fa_adddup2,
    posix_spawn_fa_addclose,
    posix_spawn_fa_addchdir,
    posix_spawnattr_init,
    posix_spawnattr_destroy,
    posix_spawnattr_setflags,
    posix_spawn,
    posix_spawnp,
    posix_waitpid,
    posix_kill,
    posix_syscall,
    posix_exit,
};

/// Discriminant for host resources stored in `VmHostSysState.win_handles`.
const WinSlotKind = enum(u8) {
    free = 0,
    os_handle = 1,
    find_handle = 2,
    reg_key = 3,
    module_handle = 4,
};

/// Tracked Windows host handle slot mapped to `dangling_empty_alloc + HANDLE_SLOT_BASE + idx`.
const WinHandleSlot = struct {
    /// Resource category stored in `raw_bits`.
    kind: WinSlotKind = .free,
    /// Host `HANDLE` / `HKEY` / `HMODULE` integer value.
    raw_bits: usize = 0,
};

/// Active memory-mapped view bridging a `MirVm` allocation to a host `MapViewOfFile` or `mmap` region.
const MappedViewRecord = struct {
    /// `MirVm` allocation backing the slice visible to `.cx` code.
    vm_alloc: ComptimeAllocId,
    /// Host pointer returned by `MapViewOfFile` or `mmap` (`0` when empty-copy-only).
    host_addr: usize = 0,
    /// Mapped byte length.
    byte_len: usize = 0,
};

/// Pending asynchronous `ReadDirectoryChangesW` operation bridged between host Win32 and `MirVm`.
const WinPendingWatch = struct {
    /// Directory `MirVm` handle offset (`HANDLE_SLOT_BASE + idx`).
    dir_token: u32,
    /// Destination `notify_buf_out` inside `MirVm`.
    vm_notify_buf: SymbolicPtr,
    /// `OVERLAPPED*` address inside `MirVm`.
    vm_overlapped: SymbolicPtr,
    /// Host-allocated notification bounce buffer (`notify_cap` bytes).
    host_buf: []u8,
    /// Heap-pinned 32-byte Win32 `OVERLAPPED` passed to kernel `ReadDirectoryChangesW`.
    host_overlapped: *[4]usize,
};

/// Per-`MirVm` host OS state owned by `MirVm.host_sys_state` during `is_oracle_runtime_mode` runs.
pub const VmHostSysState = struct {
    /// Lazily allocated `4`-byte mutable `errno` cell inside `MirVm` memory.
    errno_alloc: ComptimeAllocId = .none,
    /// Lazily allocated `_cx_rt_get_argv()` pointer table inside `MirVm` memory.
    argv_alloc: ComptimeAllocId = .none,
    /// Lazily allocated UTF-16 command line inside `MirVm` memory (`GetCommandLineW`).
    cmdline_w_alloc: ComptimeAllocId = .none,
    /// Thread-local Win32 error code (`GetLastError` / `SetLastError`).
    win_last_error: u32 = 0,
    /// Bounded table of open Win32/NT/Registry handles (`<= MAX_HOST_HANDLES`).
    win_handles: std.ArrayListUnmanaged(WinHandleSlot) = .empty,
    /// Active mapped file views (`MapViewOfFile` / `mmap`).
    mapped_views: std.ArrayListUnmanaged(MappedViewRecord) = .empty,
    /// Active overlapped `ReadDirectoryChangesW` buffers on Windows.
    win_watches: std.ArrayListUnmanaged(WinPendingWatch) = .empty,
    /// Host-side `LPPROC_THREAD_ATTRIBUTE_LIST` buffers keyed by `vm_attr_ptr` virtual address.
    win_proc_attrs: std.AutoHashMapUnmanaged(u64, []align(8) u8) = .empty,
    /// Tracked POSIX file descriptors opened during this `MirVm` run (closed on teardown if still open).
    posix_open_fds: std.AutoHashMapUnmanaged(i32, void) = .empty,
    /// In-VM POSIX environment overrides (`key -> NUL-terminated MirVm pointer`).
    posix_env_ptrs: std.StringHashMapUnmanaged(SymbolicPtr) = .empty,

    /// Releases all remaining host descriptors, mapped views, and scratch allocations.
    pub fn deinit(self: *VmHostSysState, allocator: std.mem.Allocator) void {
        if (builtin.os.tag == .windows) {
            for (self.win_watches.items) |watch_rec| {
                if (resolveRawWinHandleOpt(self, watch_rec.dir_token, .os_handle)) |dir_h| {
                    _ = win32.CancelIoEx(@ptrFromInt(dir_h), @ptrCast(watch_rec.host_overlapped));
                }
                allocator.free(watch_rec.host_buf);
                allocator.destroy(watch_rec.host_overlapped);
            }
            for (self.mapped_views.items) |view| {
                if (view.host_addr != 0) {
                    _ = win32.UnmapViewOfFile(@ptrFromInt(view.host_addr));
                }
            }
            for (self.win_handles.items) |slot| {
                switch (slot.kind) {
                    .free, .module_handle => {},
                    .os_handle => _ = win32.CloseHandle(@ptrFromInt(slot.raw_bits)),
                    .find_handle => _ = win32.FindClose(@ptrFromInt(slot.raw_bits)),
                    .reg_key => _ = advapi32.RegCloseKey(@ptrFromInt(slot.raw_bits)),
                }
            }
        } else if (builtin.os.tag == .linux) {
            for (self.mapped_views.items) |view| {
                if (view.host_addr != 0 and view.byte_len > 0) {
                    _ = std.os.linux.munmap(@ptrFromInt(view.host_addr), view.byte_len);
                }
            }
            var fd_it = self.posix_open_fds.keyIterator();
            while (fd_it.next()) |fd_ptr| {
                if (fd_ptr.* >= 3) _ = std.os.linux.close(fd_ptr.*);
            }
        } else if (builtin.os.tag == .macos) {
            for (self.mapped_views.items) |view| {
                if (view.host_addr != 0 and view.byte_len > 0) {
                    _ = darwin_c.munmap(@ptrFromInt(view.host_addr), view.byte_len);
                }
            }
            var fd_it = self.posix_open_fds.keyIterator();
            while (fd_it.next()) |fd_ptr| {
                if (fd_ptr.* >= 3) _ = darwin_c.close(fd_ptr.*);
            }
        }

        var attr_it = self.win_proc_attrs.valueIterator();
        while (attr_it.next()) |buf_ptr| {
            if (builtin.os.tag == .windows) {
                win32.DeleteProcThreadAttributeList(@ptrCast(buf_ptr.*.ptr));
            }
            allocator.free(buf_ptr.*);
        }
        self.win_proc_attrs.deinit(allocator);

        var env_it = self.posix_env_ptrs.keyIterator();
        while (env_it.next()) |key_ptr| {
            allocator.free(key_ptr.*);
        }
        self.posix_env_ptrs.deinit(allocator);
        self.posix_open_fds.deinit(allocator);
        self.win_watches.deinit(allocator);
        self.mapped_views.deinit(allocator);
        self.win_handles.deinit(allocator);
        self.* = .{};
    }
};

// --------------------- OS FFI Prototypes ----------------------

/// Direct Win32 `kernel32.dll` C-ABI declarations compiled only when targeting a Windows host.
const win32 = if (builtin.os.tag == .windows) struct {
    extern "kernel32" fn GetLastError() callconv(.winapi) u32;
    extern "kernel32" fn SetLastError(err_code: u32) callconv(.winapi) void;
    extern "kernel32" fn GetStdHandle(std_id: u32) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn CreateFileW(
        name: [*:0]const u16,
        access: u32,
        share: u32,
        sec: ?*const anyopaque,
        disp: u32,
        flags: u32,
        tmpl: ?*anyopaque,
    ) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn ReadFile(
        handle: *anyopaque,
        buf: [*]u8,
        len: u32,
        read_out: ?*u32,
        ov: ?*anyopaque,
    ) callconv(.winapi) i32;
    extern "kernel32" fn WriteFile(
        handle: *anyopaque,
        buf: [*]const u8,
        len: u32,
        written_out: ?*u32,
        ov: ?*anyopaque,
    ) callconv(.winapi) i32;
    extern "kernel32" fn FlushFileBuffers(handle: *anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn CloseHandle(handle: *anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn SetFilePointerEx(handle: *anyopaque, dist: i64, new_pos: ?*i64, method: u32) callconv(.winapi) i32;
    extern "kernel32" fn SetEndOfFile(handle: *anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn GetFileInformationByHandle(handle: *anyopaque, info_out: [*]u8) callconv(.winapi) i32;
    extern "kernel32" fn GetFileInformationByHandleEx(handle: *anyopaque, cls: i32, out: [*]u8, cap: u32) callconv(.winapi) i32;
    extern "kernel32" fn SetFileInformationByHandle(handle: *anyopaque, cls: i32, buf: [*]const u8, len: u32) callconv(.winapi) i32;
    extern "kernel32" fn GetFileAttributesW(path: [*:0]const u16) callconv(.winapi) u32;
    extern "kernel32" fn SetFileAttributesW(path: [*:0]const u16, attrs: u32) callconv(.winapi) i32;
    extern "kernel32" fn GetFileAttributesExW(path: [*:0]const u16, level: i32, out: [*]u8) callconv(.winapi) i32;
    extern "kernel32" fn GetFinalPathNameByHandleW(handle: *anyopaque, out: [*]u16, cap: u32, flags: u32) callconv(.winapi) u32;
    extern "kernel32" fn GetFullPathNameW(name: [*:0]const u16, cap: u32, out: [*]u16, part: ?*?[*]u16) callconv(.winapi) u32;
    extern "kernel32" fn MoveFileExW(src: [*:0]const u16, dst: ?[*:0]const u16, flags: u32) callconv(.winapi) i32;
    extern "kernel32" fn ReplaceFileW(
        replaced: [*:0]const u16,
        replacement: [*:0]const u16,
        backup: ?[*:0]const u16,
        flags: u32,
        excl: ?*anyopaque,
        res: ?*anyopaque,
    ) callconv(.winapi) i32;
    extern "kernel32" fn DeleteFileW(path: [*:0]const u16) callconv(.winapi) i32;
    extern "kernel32" fn CreateDirectoryW(path: [*:0]const u16, sec: ?*const anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn RemoveDirectoryW(path: [*:0]const u16) callconv(.winapi) i32;
    extern "kernel32" fn CreateHardLinkW(new_p: [*:0]const u16, old_p: [*:0]const u16, sec: ?*anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn DeviceIoControl(
        dev: *anyopaque,
        code: u32,
        in_b: ?[*]const u8,
        in_l: u32,
        out_b: ?[*]u8,
        out_l: u32,
        ret_out: ?*u32,
        ov: ?*anyopaque,
    ) callconv(.winapi) i32;
    extern "kernel32" fn FindFirstFileExW(
        pat: [*:0]const u16,
        info_lvl: i32,
        out_data: [*]u8,
        op: i32,
        flt: ?*anyopaque,
        flags: u32,
    ) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn FindNextFileW(handle: *anyopaque, out_data: [*]u8) callconv(.winapi) i32;
    extern "kernel32" fn FindClose(handle: *anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn CreateFileMappingW(
        file_h: *anyopaque,
        sec: ?*const anyopaque,
        prot: u32,
        max_hi: u32,
        max_lo: u32,
        name: ?[*:0]const u16,
    ) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn MapViewOfFile(map_h: *anyopaque, access: u32, hi: u32, lo: u32, bytes: usize) callconv(.winapi) ?[*]u8;
    extern "kernel32" fn UnmapViewOfFile(addr: *const anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn LockFileEx(file_h: *anyopaque, flags: u32, res: u32, lo: u32, hi: u32, ov: [*]u8) callconv(.winapi) i32;
    extern "kernel32" fn UnlockFileEx(file_h: *anyopaque, res: u32, lo: u32, hi: u32, ov: [*]u8) callconv(.winapi) i32;
    extern "kernel32" fn ReadDirectoryChangesW(
        dir_h: *anyopaque,
        buf: [*]u8,
        len: u32,
        sub: i32,
        flt: u32,
        ret_out: ?*u32,
        ov: ?*anyopaque,
        comp: ?*anyopaque,
    ) callconv(.winapi) i32;
    extern "kernel32" fn CreateEventW(sec: ?*const anyopaque, manual: i32, init_st: i32, name: ?[*:0]const u16) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn WaitForSingleObject(handle: *anyopaque, timeout_ms: u32) callconv(.winapi) u32;
    extern "kernel32" fn GetOverlappedResult(handle: *anyopaque, ov: *anyopaque, xfer: *u32, wait_f: i32) callconv(.winapi) i32;
    extern "kernel32" fn CancelIoEx(handle: *anyopaque, ov: ?*const anyopaque) callconv(.winapi) i32;
    extern "kernel32" fn GetConsoleMode(handle: *anyopaque, mode_out: *u32) callconv(.winapi) i32;
    extern "kernel32" fn GetFileType(handle: *anyopaque) callconv(.winapi) u32;
    extern "kernel32" fn QueryPerformanceCounter(out: *i64) callconv(.winapi) i32;
    extern "kernel32" fn QueryPerformanceFrequency(out: *i64) callconv(.winapi) i32;
    extern "kernel32" fn GetSystemTimePreciseAsFileTime(out: *[2]u32) callconv(.winapi) void;
    extern "kernel32" fn Sleep(ms: u32) callconv(.winapi) void;
    extern "kernel32" fn GetEnvironmentStringsW() callconv(.winapi) ?[*]u16;
    extern "kernel32" fn FreeEnvironmentStringsW(blk: [*]u16) callconv(.winapi) i32;
    extern "kernel32" fn GetEnvironmentVariableW(key: [*:0]const u16, out: ?[*]u16, cap: u32) callconv(.winapi) u32;
    extern "kernel32" fn SetEnvironmentVariableW(key: [*:0]const u16, val: ?[*:0]const u16) callconv(.winapi) i32;
    extern "kernel32" fn ExpandEnvironmentStringsW(src: [*:0]const u16, dst: ?[*]u16, cap: u32) callconv(.winapi) u32;
    extern "kernel32" fn GetCurrentDirectoryW(cap: u32, out: ?[*]u16) callconv(.winapi) u32;
    extern "kernel32" fn SetCurrentDirectoryW(path: [*:0]const u16) callconv(.winapi) i32;
    extern "kernel32" fn GetModuleFileNameW(mod_h: ?*anyopaque, out: [*]u16, cap: u32) callconv(.winapi) u32;
    extern "kernel32" fn GetTempPathW(cap: u32, out: ?[*]u16) callconv(.winapi) u32;
    extern "kernel32" fn GetModuleHandleW(name: ?[*:0]const u16) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn GetProcAddress(mod_h: *anyopaque, name: [*:0]const u8) callconv(.winapi) ?*anyopaque;
    extern "kernel32" fn GetCurrentProcessId() callconv(.winapi) u32;
    extern "kernel32" fn CreatePipe(rd: *?*anyopaque, wr: *?*anyopaque, sec: ?*const anyopaque, sz: u32) callconv(.winapi) i32;
    extern "kernel32" fn SetHandleInformation(handle: *anyopaque, mask: u32, flags: u32) callconv(.winapi) i32;
    extern "kernel32" fn GetHandleInformation(handle: *anyopaque, flags_out: *u32) callconv(.winapi) i32;
    extern "kernel32" fn SearchPathW(
        dirs: ?[*:0]const u16,
        file: [*:0]const u16,
        ext: ?[*:0]const u16,
        cap: u32,
        out: ?[*]u16,
        part: ?*?[*]u16,
    ) callconv(.winapi) u32;
    extern "kernel32" fn InitializeProcThreadAttributeList(list: ?*anyopaque, cnt: u32, flags: u32, sz: *usize) callconv(.winapi) i32;
    extern "kernel32" fn UpdateProcThreadAttribute(
        list: *anyopaque,
        flags: u32,
        attr: usize,
        val: *anyopaque,
        cb: usize,
        prev: ?*anyopaque,
        ret_sz: ?*usize,
    ) callconv(.winapi) i32;
    extern "kernel32" fn DeleteProcThreadAttributeList(list: *anyopaque) callconv(.winapi) void;
    extern "kernel32" fn CreateProcessW(
        app: ?[*:0]const u16,
        cmd: ?[*:0]u16,
        p_sec: ?*const anyopaque,
        t_sec: ?*const anyopaque,
        inh: i32,
        flags: u32,
        env: ?*const anyopaque,
        cwd: ?[*:0]const u16,
        si: *const anyopaque,
        pi_out: *[4]usize,
    ) callconv(.winapi) i32;
    extern "kernel32" fn GetExitCodeProcess(proc_h: *anyopaque, code_out: *u32) callconv(.winapi) i32;
    extern "kernel32" fn TerminateProcess(proc_h: *anyopaque, code: u32) callconv(.winapi) i32;
} else struct {};

/// Direct NT `ntdll.dll` C-ABI declarations compiled only when targeting a Windows host.
const ntdll = if (builtin.os.tag == .windows) struct {
    const UnicodeString = extern struct { len: u16, max_len: u16, buf: [*]u16 };
    const ObjectAttributes = extern struct {
        len: u32,
        root_dir: ?*anyopaque,
        obj_name: *UnicodeString,
        attrs: u32,
        sec_desc: ?*anyopaque,
        sec_qos: ?*anyopaque,
    };
    const IoStatusBlock = extern struct { status: usize, info: usize };
    extern "ntdll" fn NtCreateFile(
        handle_out: *?*anyopaque,
        access: u32,
        obj_attrs: *ObjectAttributes,
        io_status: *IoStatusBlock,
        alloc_size: ?*const i64,
        file_attrs: u32,
        share: u32,
        create_disp: u32,
        create_opts: u32,
        ea_buf: ?*const anyopaque,
        ea_len: u32,
    ) callconv(.winapi) i32;
    extern "ntdll" fn RtlNtStatusToDosError(status: i32) callconv(.winapi) u32;
} else struct {};

/// Direct Windows Registry `advapi32.dll` declarations compiled only when targeting a Windows host.
const advapi32 = if (builtin.os.tag == .windows) struct {
    extern "advapi32" fn RegOpenKeyExW(
        root: *anyopaque,
        subkey: [*:0]const u16,
        opts: u32,
        sam: u32,
        out: *?*anyopaque,
    ) callconv(.winapi) i32;
    extern "advapi32" fn RegQueryValueExW(
        key: *anyopaque,
        val_name: ?[*:0]const u16,
        res: ?*u32,
        ty_out: ?*u32,
        data_out: ?[*]u8,
        cb_inout: ?*u32,
    ) callconv(.winapi) i32;
    extern "advapi32" fn RegCloseKey(key: *anyopaque) callconv(.winapi) i32;
} else struct {};

/// Direct Darwin `libSystem` declarations compiled only when targeting a macOS host.
const darwin_c = if (builtin.os.tag == .macos) struct {
    extern "c" fn __error() *c_int;
    extern "c" fn openat(dir_fd: c_int, path: [*:0]const u8, flags: c_int, ...) c_int;
    extern "c" fn read(fd: c_int, buf: [*]u8, len: usize) isize;
    extern "c" fn write(fd: c_int, buf: [*]const u8, len: usize) isize;
    extern "c" fn pread(fd: c_int, buf: [*]u8, len: usize, off: i64) isize;
    extern "c" fn pwrite(fd: c_int, buf: [*]const u8, len: usize, off: i64) isize;
    extern "c" fn lseek(fd: c_int, off: i64, whence: c_int) i64;
    extern "c" fn ftruncate(fd: c_int, sz: i64) c_int;
    extern "c" fn fchmod(fd: c_int, mode: u16) c_int;
    extern "c" fn fcntl(fd: c_int, cmd: c_int, ...) c_int;
    extern "c" fn fsync(fd: c_int) c_int;
    extern "c" fn close(fd: c_int) c_int;
    extern "c" fn renameat(old_fd: c_int, old_p: [*:0]const u8, new_fd: c_int, new_p: [*:0]const u8) c_int;
    extern "c" fn unlinkat(dir_fd: c_int, path: [*:0]const u8, flags: c_int) c_int;
    extern "c" fn mkdirat(dir_fd: c_int, path: [*:0]const u8, mode: u16) c_int;
    extern "c" fn linkat(old_fd: c_int, old_p: [*:0]const u8, new_fd: c_int, new_p: [*:0]const u8, flags: c_int) c_int;
    extern "c" fn symlinkat(target: [*:0]const u8, new_fd: c_int, link_p: [*:0]const u8) c_int;
    extern "c" fn readlinkat(dir_fd: c_int, path: [*:0]const u8, out: [*]u8, cap: usize) isize;
    extern "c" fn realpath(path: [*:0]const u8, out: [*]u8) ?[*]u8;
    extern "c" fn getcwd(out: [*]u8, cap: usize) ?[*]u8;
    extern "c" fn chdir(path: [*:0]const u8) c_int;
    extern "c" fn clonefileat(src_fd: c_int, src_p: [*:0]const u8, dst_fd: c_int, dst_p: [*:0]const u8, flags: u32) c_int;
    extern "c" fn fcopyfile(src_fd: c_int, dst_fd: c_int, state: ?*anyopaque, flags: u32) c_int;
    extern "c" fn mmap(addr: ?*anyopaque, len: usize, prot: c_int, flags: c_int, fd: c_int, off: i64) ?*anyopaque;
    extern "c" fn munmap(addr: *anyopaque, len: usize) c_int;
    extern "c" fn flock(fd: c_int, op: c_int) c_int;
    extern "c" fn kqueue() c_int;
    extern "c" fn kevent64(kq: c_int, chg: ?*const anyopaque, nchg: c_int, ev: ?*anyopaque, nev: c_int, flg: u32, to: ?*const anyopaque) c_int;
    extern "c" fn poll(fds: [*]u8, nfds: u32, timeout_ms: c_int) c_int;
    extern "c" fn isatty(fd: c_int) c_int;
    extern "c" fn stat(path: [*:0]const u8, out: [*]u8) c_int;
    extern "c" fn fstat(fd: c_int, out: [*]u8) c_int;
    extern "c" fn lstat(path: [*:0]const u8, out: [*]u8) c_int;
    extern "c" fn fstatat(dir_fd: c_int, path: [*:0]const u8, out: [*]u8, flags: c_int) c_int;
    extern "c" fn __getdirentries64(fd: c_int, buf: [*]u8, bytes: usize, basep: *i64) isize;
    extern "c" fn clock_gettime(clk_id: c_int, tp_out: *[2]i64) c_int;
    extern "c" fn clock_gettime_nsec_np(clk_id: c_int) u64;
    extern "c" fn mach_continuous_time() u64;
    extern "c" fn mach_timebase_info(info_out: *[2]u32) c_int;
    extern "c" fn nanosleep(req: *const [2]i64, rem: ?*[2]i64) c_int;
    extern "c" fn getenv(key: [*:0]const u8) ?[*:0]u8;
    extern "c" fn setenv(key: [*:0]const u8, val: [*:0]const u8, overwrite: c_int) c_int;
    extern "c" fn unsetenv(key: [*:0]const u8) c_int;
    extern "c" fn _NSGetExecutablePath(out: [*]u8, sz_inout: *u32) c_int;
    extern "c" fn _NSGetEnviron() *?[*:null]?[*:0]u8;
    extern "c" fn getpid() c_int;
    extern "c" fn pipe(fds: *[2]c_int) c_int;
    extern "c" fn posix_spawn_file_actions_init(fa: *?*anyopaque) c_int;
    extern "c" fn posix_spawn_file_actions_destroy(fa: *?*anyopaque) c_int;
    extern "c" fn posix_spawn_file_actions_adddup2(fa: *?*anyopaque, fd: c_int, new_fd: c_int) c_int;
    extern "c" fn posix_spawn_file_actions_addclose(fa: *?*anyopaque, fd: c_int) c_int;
    extern "c" fn posix_spawn_file_actions_addchdir_np(fa: *?*anyopaque, path: [*:0]const u8) c_int;
    extern "c" fn posix_spawnattr_init(attr: *?*anyopaque) c_int;
    extern "c" fn posix_spawnattr_destroy(attr: *?*anyopaque) c_int;
    extern "c" fn posix_spawnattr_setflags(attr: *?*anyopaque, flags: i16) c_int;
    extern "c" fn posix_spawn(
        pid: *c_int,
        path: [*:0]const u8,
        fa: ?*const ?*anyopaque,
        attr: ?*const ?*anyopaque,
        argv: [*:null]const ?[*:0]const u8,
        envp: ?[*:null]const ?[*:0]const u8,
    ) c_int;
    extern "c" fn posix_spawnp(
        pid: *c_int,
        file: [*:0]const u8,
        fa: ?*const ?*anyopaque,
        attr: ?*const ?*anyopaque,
        argv: [*:null]const ?[*:0]const u8,
        envp: ?[*:null]const ?[*:0]const u8,
    ) c_int;
    extern "c" fn waitpid(pid: c_int, status_out: ?*c_int, opts: c_int) c_int;
    extern "c" fn kill(pid: c_int, sig: c_int) c_int;
} else struct {};

// --------------------------------------- CONSTS ----------------------------------------

/// Maximum host handles tracked simultaneously inside a single `MirVm` oracle execution.
const MAX_HOST_HANDLES: usize = 4_096;
/// Maximum C-string or UTF-16 path length marshaled across the `MirVm` FFI boundary.
const MAX_SHIM_PATH_UNITS: usize = 32_768;
/// Maximum UTF-16 code units in a Win32 `lpEnvironment` block marshaled across the `MirVm` FFI boundary.
const MAX_SHIM_ENV_UNITS: usize = 262_144;
/// Base `byte_offset` on `dangling_empty_alloc` for standard input (`0x0001_0000`).
const STD_IN_TOKEN: u32 = 0x0001_0000;
/// Base `byte_offset` on `dangling_empty_alloc` for standard output (`0x0001_0001`).
const STD_OUT_TOKEN: u32 = 0x0001_0001;
/// Base `byte_offset` on `dangling_empty_alloc` for standard error (`0x0001_0002`).
const STD_ERR_TOKEN: u32 = 0x0001_0002;
/// Base `byte_offset` on `dangling_empty_alloc` for allocated `win_handles` slots (`0x0002_0000 + idx`).
const HANDLE_SLOT_BASE: u32 = 0x0002_0000;

/// $O(1)$ lookup table mapping `@link(name: "…")` extern symbols in `core.sys` to `ShimOp`.
const SHIM_OP_MAP = std.StaticStringMap(ShimOp).initComptime(.{
    .{ "CancelIoEx", .win_cancel_io_ex },
    .{ "CloseHandle", .win_close_handle },
    .{ "CreateDirectoryW", .win_create_directory_w },
    .{ "CreateEventW", .win_create_event_w },
    .{ "CreateFileMappingW", .win_create_file_mapping_w },
    .{ "CreateFileW", .win_create_file_w },
    .{ "CreateHardLinkW", .win_create_hard_link_w },
    .{ "CreatePipe", .win_create_pipe },
    .{ "CreateProcessW", .win_create_process_w },
    .{ "DeleteFileW", .win_delete_file_w },
    .{ "DeleteProcThreadAttributeList", .win_delete_proc_thread_attr_list },
    .{ "DeviceIoControl", .win_device_io_control },
    .{ "ExitProcess", .win_exit_process },
    .{ "ExpandEnvironmentStringsW", .win_expand_environment_strings_w },
    .{ "FindClose", .win_find_close },
    .{ "FindFirstFileExW", .win_find_first_file_ex_w },
    .{ "FindNextFileW", .win_find_next_file_w },
    .{ "FlushFileBuffers", .win_flush_file_buffers },
    .{ "FreeEnvironmentStringsW", .win_free_environment_strings_w },
    .{ "GetCommandLineW", .win_get_command_line_w },
    .{ "GetConsoleMode", .win_get_console_mode },
    .{ "GetCurrentDirectoryW", .win_get_current_directory_w },
    .{ "GetCurrentProcessId", .win_get_current_process_id },
    .{ "GetEnvironmentStringsW", .win_get_environment_strings_w },
    .{ "GetEnvironmentVariableW", .win_get_environment_variable_w },
    .{ "GetExitCodeProcess", .win_get_exit_code_process },
    .{ "GetFileAttributesExW", .win_get_file_attributes_ex_w },
    .{ "GetFileAttributesW", .win_get_file_attributes_w },
    .{ "GetFileInformationByHandle", .win_get_file_info_by_handle },
    .{ "GetFileInformationByHandleEx", .win_get_file_info_by_handle_ex },
    .{ "GetFileType", .win_get_file_type },
    .{ "GetFinalPathNameByHandleW", .win_get_final_path_name_w },
    .{ "GetFullPathNameW", .win_get_full_path_name_w },
    .{ "GetHandleInformation", .win_get_handle_information },
    .{ "GetLastError", .win_get_last_error },
    .{ "GetModuleFileNameW", .win_get_module_file_name_w },
    .{ "GetModuleHandleW", .win_get_module_handle_w },
    .{ "GetOverlappedResult", .win_get_overlapped_result },
    .{ "GetProcAddress", .win_get_proc_address },
    .{ "GetStdHandle", .win_get_std_handle },
    .{ "GetSystemTimePreciseAsFileTime", .win_get_system_time_precise },
    .{ "GetTempPathW", .win_get_temp_path_w },
    .{ "InitializeProcThreadAttributeList", .win_init_proc_thread_attr_list },
    .{ "LockFileEx", .win_lock_file_ex },
    .{ "MapViewOfFile", .win_map_view_of_file },
    .{ "MoveFileExW", .win_move_file_ex_w },
    .{ "NtCreateFile", .win_nt_create_file },
    .{ "QueryPerformanceCounter", .win_query_performance_counter },
    .{ "QueryPerformanceFrequency", .win_query_performance_frequency },
    .{ "ReadDirectoryChangesW", .win_read_directory_changes_w },
    .{ "ReadFile", .win_read_file },
    .{ "RegCloseKey", .win_reg_close_key },
    .{ "RegOpenKeyExW", .win_reg_open_key_ex_w },
    .{ "RegQueryValueExW", .win_reg_query_value_ex_w },
    .{ "RemoveDirectoryW", .win_remove_directory_w },
    .{ "ReplaceFileW", .win_replace_file_w },
    .{ "RtlNtStatusToDosError", .win_rtl_nt_status_to_dos_error },
    .{ "SearchPathW", .win_search_path_w },
    .{ "SetCurrentDirectoryW", .win_set_current_directory_w },
    .{ "SetEndOfFile", .win_set_end_of_file },
    .{ "SetEnvironmentVariableW", .win_set_environment_variable_w },
    .{ "SetFileAttributesW", .win_set_file_attributes_w },
    .{ "SetFileInformationByHandle", .win_set_file_info_by_handle },
    .{ "SetFilePointerEx", .win_set_file_pointer_ex },
    .{ "SetHandleInformation", .win_set_handle_information },
    .{ "SetLastError", .win_set_last_error },
    .{ "Sleep", .win_sleep },
    .{ "TerminateProcess", .win_terminate_process },
    .{ "UnlockFileEx", .win_unlock_file_ex },
    .{ "UnmapViewOfFile", .win_unmap_view_of_file },
    .{ "UpdateProcThreadAttribute", .win_update_proc_thread_attr },
    .{ "WaitForSingleObject", .win_wait_for_single_object },
    .{ "WriteFile", .win_write_file },
    .{ "_NSGetEnviron", .posix_ns_get_environ },
    .{ "_NSGetExecutablePath", .posix_ns_get_executable_path },
    .{ "__errno_location", .posix_errno_location },
    .{ "__error", .posix_errno_location },
    .{ "__getdirentries64", .posix_getdirentries64 },
    .{ "_cx_rt_get_argc", .rt_get_argc },
    .{ "_cx_rt_get_argv", .rt_get_argv },
    .{ "_exit", .posix_exit },
    .{ "chdir", .posix_chdir },
    .{ "clock_gettime", .posix_clock_gettime },
    .{ "clock_gettime_nsec_np", .posix_clock_gettime_nsec_np },
    .{ "clonefileat", .posix_clonefileat },
    .{ "close", .posix_close },
    .{ "copy_file_range", .posix_copy_file_range },
    .{ "dlsym", .posix_dlsym },
    .{ "fchmod", .posix_fchmod },
    .{ "fcntl", .posix_fcntl },
    .{ "fcopyfile", .posix_fcopyfile },
    .{ "fdatasync", .posix_fdatasync },
    .{ "flock", .posix_flock },
    .{ "fstat", .posix_fstat },
    .{ "fstat$INODE64", .posix_fstat },
    .{ "fstatat", .posix_fstatat },
    .{ "fstatat$INODE64", .posix_fstatat },
    .{ "fsync", .posix_fsync },
    .{ "ftruncate", .posix_ftruncate },
    .{ "getcwd", .posix_getcwd },
    .{ "getenv", .posix_getenv },
    .{ "getpid", .posix_getpid },
    .{ "inotify_add_watch", .posix_inotify_add_watch },
    .{ "inotify_init1", .posix_inotify_init1 },
    .{ "inotify_rm_watch", .posix_inotify_rm_watch },
    .{ "ioctl", .posix_ioctl },
    .{ "isatty", .posix_isatty },
    .{ "kevent64", .posix_kevent64 },
    .{ "kill", .posix_kill },
    .{ "kqueue", .posix_kqueue },
    .{ "linkat", .posix_linkat },
    .{ "lseek", .posix_lseek },
    .{ "lstat", .posix_lstat },
    .{ "lstat$INODE64", .posix_lstat },
    .{ "mach_continuous_time", .posix_mach_continuous_time },
    .{ "mach_timebase_info", .posix_mach_timebase_info },
    .{ "mkdirat", .posix_mkdirat },
    .{ "mmap", .posix_mmap },
    .{ "munmap", .posix_munmap },
    .{ "nanosleep", .posix_nanosleep },
    .{ "openat", .posix_openat },
    .{ "pipe", .posix_pipe },
    .{ "pipe2", .posix_pipe2 },
    .{ "poll", .posix_poll },
    .{ "posix_spawn", .posix_spawn },
    .{ "posix_spawn_file_actions_addchdir_np", .posix_spawn_fa_addchdir },
    .{ "posix_spawn_file_actions_addclose", .posix_spawn_fa_addclose },
    .{ "posix_spawn_file_actions_adddup2", .posix_spawn_fa_adddup2 },
    .{ "posix_spawn_file_actions_destroy", .posix_spawn_fa_destroy },
    .{ "posix_spawn_file_actions_init", .posix_spawn_fa_init },
    .{ "posix_spawnattr_destroy", .posix_spawnattr_destroy },
    .{ "posix_spawnattr_init", .posix_spawnattr_init },
    .{ "posix_spawnattr_setflags", .posix_spawnattr_setflags },
    .{ "posix_spawnp", .posix_spawnp },
    .{ "pread", .posix_pread },
    .{ "pwrite", .posix_pwrite },
    .{ "read", .posix_read },
    .{ "readlinkat", .posix_readlinkat },
    .{ "readv", .posix_readv },
    .{ "realpath", .posix_realpath },
    .{ "renameat", .posix_renameat },
    .{ "setenv", .posix_setenv },
    .{ "stat", .posix_stat },
    .{ "stat$INODE64", .posix_stat },
    .{ "symlinkat", .posix_symlinkat },
    .{ "syscall", .posix_syscall },
    .{ "unlinkat", .posix_unlinkat },
    .{ "unsetenv", .posix_unsetenv },
    .{ "waitpid", .posix_waitpid },
    .{ "write", .posix_write },
    .{ "writev", .posix_writev },
});

// -------------------------------------- INTERNALS --------------------------------------

// -------------------- VM Memory & Slot I/O --------------------

/// Lazily initializes and returns `&vm.host_sys_state.?`.
fn ensureSysState(vm: *MirVm) *VmHostSysState {
    if (vm.host_sys_state == null) {
        vm.host_sys_state = .{};
    }
    return &vm.host_sys_state.?;
}

/// Evaluates call-site argument `arg_i` into `(RegSlot, TypeId)` in `caller_body`.
fn getArgSlotAndType(
    vm: *MirVm,
    frame_idx: usize,
    call_site: mir.MirCallSite,
    arg_i: usize,
) struct { slot: RegSlot, ty: TypeId } {
    const caller_body = vm.call_stack.items[frame_idx].body;
    const word = caller_body.extra_args.items[call_site.args_start + arg_i];
    const val_id = MirValueId.fromInt(word);
    return .{
        .slot = vm.call_stack.items[frame_idx].regs[word],
        .ty = caller_body.getInst(val_id).type_id,
    };
}

/// Reads an unsigned 64-bit integer from call argument `arg_i`.
fn argU64(vm: *MirVm, frame_idx: usize, call_site: mir.MirCallSite, arg_i: usize) VmEvalError!u64 {
    const arg = getArgSlotAndType(vm, frame_idx, call_site, arg_i);
    return @truncate(try vm.readIntBitsFromSlot(arg.slot, arg.ty));
}

/// Reads a signed 64-bit integer from call argument `arg_i` (sign-extending narrower integer types).
fn argI64(vm: *MirVm, frame_idx: usize, call_site: mir.MirCallSite, arg_i: usize) VmEvalError!i64 {
    const arg = getArgSlotAndType(vm, frame_idx, call_site, arg_i);
    const raw = try vm.readIntBitsFromSlot(arg.slot, arg.ty);
    const unwrapped = vm.pool.unwrapUnderlyingType(arg.ty);
    return switch (unwrapped) {
        .i8_ty => @as(i8, @bitCast(@as(u8, @truncate(raw)))),
        .i16_ty => @as(i16, @bitCast(@as(u16, @truncate(raw)))),
        .i32_ty, .untyped_int_ty => @as(i32, @bitCast(@as(u32, @truncate(raw)))),
        .isize_ty => if (vm.options.target_layout.ptr_byte_size == 4)
            @as(i32, @bitCast(@as(u32, @truncate(raw))))
        else
            @as(i64, @bitCast(@as(u64, @truncate(raw)))),
        else => @bitCast(@as(u64, @truncate(raw))),
    };
}

/// Reads a `SymbolicPtr` from pointer call argument `arg_i`.
fn argPtr(vm: *MirVm, frame_idx: usize, call_site: mir.MirCallSite, arg_i: usize) SymbolicPtr {
    return getArgSlotAndType(vm, frame_idx, call_site, arg_i).slot.sym_ptr;
}

/// Encodes a signed `i64` return value into `ret_ty` (two's-complement masked by `makeIntSlot`).
fn retSigned(vm: *MirVm, ret_ty: TypeId, val: i64) VmEvalError!RegSlot {
    if (ret_ty == .unit_ty) return .{ .scalar_u64 = 0 };
    return vm.makeIntSlot(ret_ty, @bitCast(@as(i128, val)));
}

/// Encodes an unsigned `u64` return value into `ret_ty`.
fn retUnsigned(vm: *MirVm, ret_ty: TypeId, val: u64) VmEvalError!RegSlot {
    if (ret_ty == .unit_ty) return .{ .scalar_u64 = 0 };
    return vm.makeIntSlot(ret_ty, val);
}

/// Encodes a `SymbolicPtr` return value into `RegSlot`.
inline fn retPtr(sym_ptr: SymbolicPtr) RegSlot {
    return .{ .sym_ptr = sym_ptr };
}

/// Writes a little-endian `u32` into `MirVm` memory at `ptr`.
fn writeVmU32(vm: *MirVm, ptr: SymbolicPtr, val: u32) VmEvalError!void {
    var buf: [4]u8 = undefined;
    std.mem.writeInt(u32, &buf, val, .little);
    try vm.writeScalarBytes(ptr, 0, &buf);
}

/// Writes a little-endian `i32` into `MirVm` memory at `ptr`.
fn writeVmI32(vm: *MirVm, ptr: SymbolicPtr, val: i32) VmEvalError!void {
    var buf: [4]u8 = undefined;
    std.mem.writeInt(i32, &buf, val, .little);
    try vm.writeScalarBytes(ptr, 0, &buf);
}

/// Writes a little-endian `u64` into `MirVm` memory at `ptr`.
fn writeVmU64(vm: *MirVm, ptr: SymbolicPtr, val: u64) VmEvalError!void {
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u64, &buf, val, .little);
    try vm.writeScalarBytes(ptr, 0, &buf);
}

/// Writes a little-endian `i64` into `MirVm` memory at `ptr`.
fn writeVmI64(vm: *MirVm, ptr: SymbolicPtr, val: i64) VmEvalError!void {
    var buf: [8]u8 = undefined;
    std.mem.writeInt(i64, &buf, val, .little);
    try vm.writeScalarBytes(ptr, 0, &buf);
}

/// Writes a target-sized `usize` into `MirVm` memory at `ptr`.
fn writeVmUsize(vm: *MirVm, ptr: SymbolicPtr, val: u64) VmEvalError!void {
    if (vm.options.target_layout.ptr_byte_size == 4) {
        try writeVmU32(vm, ptr, @truncate(val));
    } else {
        try writeVmU64(vm, ptr, val);
    }
}

/// Reads a target-sized `usize` from `MirVm` memory at `ptr`.
fn readVmUsize(vm: *MirVm, ptr: SymbolicPtr) VmEvalError!u64 {
    if (vm.options.target_layout.ptr_byte_size == 4) {
        var buf: [4]u8 = undefined;
        try vm.readScalarBytes(ptr, 0, &buf);
        return std.mem.readInt(u32, &buf, .little);
    }
    var buf: [8]u8 = undefined;
    try vm.readScalarBytes(ptr, 0, &buf);
    return std.mem.readInt(u64, &buf, .little);
}

/// Reads a NUL-terminated UTF-8 C string from `ptr` in `MirVm` memory (`<= MAX_SHIM_PATH_UNITS`).
fn readVmCStringZ(vm: *MirVm, ptr: SymbolicPtr) VmEvalError![:0]u8 {
    var list: std.ArrayListUnmanaged(u8) = .empty;
    errdefer list.deinit(vm.allocator);
    var idx: u64 = 0;
    while (idx < MAX_SHIM_PATH_UNITS) : (idx += 1) {
        var byte_buf: [1]u8 = undefined;
        try vm.readScalarBytes(try vm.advanceSymbolicPtr(ptr, idx), 0, &byte_buf);
        if (byte_buf[0] == 0) {
            return list.toOwnedSliceSentinel(vm.allocator, 0) catch return error.OutOfMemory;
        }
        list.append(vm.allocator, byte_buf[0]) catch return error.OutOfMemory;
    }
    return error.ResourceLimitExceeded;
}

/// Reads a NUL-terminated UTF-16 string from `ptr` in `MirVm` memory (`<= MAX_SHIM_PATH_UNITS`).
fn readVmWideStringZ(vm: *MirVm, ptr: SymbolicPtr) VmEvalError![:0]u16 {
    var list: std.ArrayListUnmanaged(u16) = .empty;
    errdefer list.deinit(vm.allocator);
    var idx: u64 = 0;
    while (idx < MAX_SHIM_PATH_UNITS) : (idx += 1) {
        var unit_buf: [2]u8 = undefined;
        try vm.readScalarBytes(try vm.advanceSymbolicPtr(ptr, idx * 2), 0, &unit_buf);
        const unit = std.mem.readInt(u16, &unit_buf, .little);
        if (unit == 0) {
            return list.toOwnedSliceSentinel(vm.allocator, 0) catch return error.OutOfMemory;
        }
        list.append(vm.allocator, unit) catch return error.OutOfMemory;
    }
    return error.ResourceLimitExceeded;
}

/// Reads a double-`0x0000`-terminated UTF-16 Win32 environment block from `ptr` (`<= MAX_SHIM_ENV_UNITS`).
fn readVmWideEnvBlock(vm: *MirVm, ptr: SymbolicPtr) VmEvalError![]u16 {
    var list: std.ArrayListUnmanaged(u16) = .empty;
    errdefer list.deinit(vm.allocator);
    var prev_was_nul = false;
    var idx: u64 = 0;
    while (idx < MAX_SHIM_ENV_UNITS) : (idx += 1) {
        var unit_buf: [2]u8 = undefined;
        try vm.readScalarBytes(try vm.advanceSymbolicPtr(ptr, idx * 2), 0, &unit_buf);
        const unit = std.mem.readInt(u16, &unit_buf, .little);
        list.append(vm.allocator, unit) catch return error.OutOfMemory;
        if (unit == 0) {
            if (prev_was_nul) {
                return list.toOwnedSlice(vm.allocator) catch return error.OutOfMemory;
            }
            prev_was_nul = true;
        } else {
            prev_was_nul = false;
        }
    }
    return error.ResourceLimitExceeded;
}

/// Writes `units` (`u16` slice) into `MirVm` memory at `dst_ptr`.
fn writeVmWideUnits(vm: *MirVm, dst_ptr: SymbolicPtr, units: []const u16) VmEvalError!void {
    if (units.len == 0) return;
    const byte_buf = vm.allocator.alloc(u8, units.len * 2) catch return error.OutOfMemory;
    defer vm.allocator.free(byte_buf);
    for (units, 0..) |unit, i| {
        std.mem.writeInt(u16, byte_buf[i * 2 ..][0..2], unit, .little);
    }
    try vm.writeScalarBytes(dst_ptr, 0, byte_buf);
}

/// Marshals `Win32SecurityAttributes` (`nLength`, `lpSecurityDescriptor`, `bInheritHandle`) skipping ABI padding.
fn readVmWin32SecurityAttrs(vm: *MirVm, sec_ptr: SymbolicPtr, sec_out: *[24]u8) VmEvalError!void {
    sec_out.* = @splat(0);
    try vm.readScalarBytes(sec_ptr, 0, sec_out[0..4]);
    const inherit_off: usize = if (vm.options.target_layout.ptr_byte_size == 4) 8 else 16;
    try vm.readScalarBytes(try vm.advanceSymbolicPtr(sec_ptr, inherit_off), 0, sec_out[inherit_off .. inherit_off + 4]);
}

/// Allocates a persistent NUL-terminated C string inside `MirVm` memory (`is_stack_frame = false`).
fn allocVmCString(vm: *MirVm, bytes: []const u8, span: Span) VmEvalError!SymbolicPtr {
    const aid = try vm.allocMemory(bytes.len + 1, 0, true, false, false, 0, span);
    const base_ptr = SymbolicPtr{ .alloc_id = aid, .byte_offset = 0 };
    if (bytes.len > 0) {
        try vm.writeScalarBytes(base_ptr, 0, bytes);
    }
    try vm.writeScalarBytes(try vm.advanceSymbolicPtr(base_ptr, bytes.len), 0, &[1]u8{0});
    return base_ptr;
}

/// Ensures `sys_st.errno_alloc` exists and writes `err_val` into it.
fn setVmErrno(vm: *MirVm, err_val: i32, span: Span) VmEvalError!SymbolicPtr {
    const sys_st = ensureSysState(vm);
    if (sys_st.errno_alloc == .none) {
        sys_st.errno_alloc = try vm.allocMemory(4, 2, true, false, false, 0, span);
        try writeVmI32(vm, .{ .alloc_id = sys_st.errno_alloc, .byte_offset = 0 }, 0);
    }
    const errno_ptr = SymbolicPtr{ .alloc_id = sys_st.errno_alloc, .byte_offset = 0 };
    try writeVmI32(vm, errno_ptr, err_val);
    return errno_ptr;
}

/// Returns the `INVALID_HANDLE_VALUE` `SymbolicPtr` (`byte_offset = maxInt(u32)` on `dangling_empty_alloc`).
inline fn invalidWinHandlePtr(vm: *const MirVm) SymbolicPtr {
    return .{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = std.math.maxInt(u32) };
}

/// Registers a non-invalid host Windows handle into `sys_st.win_handles` and returns its `SymbolicPtr`.
fn registerWinHandle(vm: *MirVm, kind: WinSlotKind, raw_bits: usize) VmEvalError!SymbolicPtr {
    const sys_st = ensureSysState(vm);
    for (sys_st.win_handles.items, 0..) |*slot, i| {
        if (slot.kind == .free) {
            slot.* = .{ .kind = kind, .raw_bits = raw_bits };
            return .{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = HANDLE_SLOT_BASE + @as(u32, @intCast(i)) };
        }
    }
    if (sys_st.win_handles.items.len >= MAX_HOST_HANDLES) return error.ResourceLimitExceeded;
    const idx: u32 = @intCast(sys_st.win_handles.items.len);
    sys_st.win_handles.append(vm.allocator, .{ .kind = kind, .raw_bits = raw_bits }) catch return error.OutOfMemory;
    return .{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = HANDLE_SLOT_BASE + idx };
}

/// Looks up a raw Windows handle from `token_offset` (`HANDLE_SLOT_BASE + idx`) without consuming it.
fn resolveRawWinHandleOpt(sys_st: *const VmHostSysState, token_offset: u32, wanted: WinSlotKind) ?usize {
    if (token_offset < HANDLE_SLOT_BASE) return null;
    const idx: usize = token_offset - HANDLE_SLOT_BASE;
    if (idx >= sys_st.win_handles.items.len) return null;
    const slot = sys_st.win_handles.items[idx];
    if (slot.kind != wanted) return null;
    return slot.raw_bits;
}

/// Resolves a `SymbolicPtr` Win32 handle (including `STD_*_HANDLE` tokens) to its host `HANDLE` pointer.
fn resolveWinOsHandle(vm: *MirVm, handle_ptr: SymbolicPtr) ?*anyopaque {
    if (builtin.os.tag != .windows) return null;
    if (handle_ptr.alloc_id != vm.dangling_empty_alloc) return null;
    if (handle_ptr.byte_offset == STD_IN_TOKEN) return win32.GetStdHandle(0xFFFF_FFF6);
    if (handle_ptr.byte_offset == STD_OUT_TOKEN) return win32.GetStdHandle(0xFFFF_FFF5);
    if (handle_ptr.byte_offset == STD_ERR_TOKEN) return win32.GetStdHandle(0xFFFF_FFF4);
    if (resolveRawWinHandleOpt(ensureSysState(vm), handle_ptr.byte_offset, .os_handle)) |bits| {
        return @ptrFromInt(bits);
    }
    return null;
}

/// Evaluates `_cx_rt_get_argc` / `_cx_rt_get_argv` matching `diff_oracle`'s 1-arg `[exe_path, null]` launch.
fn evalRuntimeProcessArgs(vm: *MirVm, op: ShimOp, ret_ty: TypeId, span: Span) VmEvalError!RegSlot {
    if (op == .rt_get_argc) {
        return retSigned(vm, ret_ty, 1);
    }
    const sys_st = ensureSysState(vm);
    if (sys_st.argv_alloc == .none) {
        const ptr_bytes: u64 = vm.options.target_layout.ptr_byte_size;
        const ptr_align = vm.options.target_layout.ptr_align_log2;
        const table_aid = try vm.allocMemory(ptr_bytes * 2, ptr_align, true, false, false, 0, span);
        const arg0_ptr = try allocVmCString(vm, "corex_oracle", span);
        const slot0 = SymbolicPtr{ .alloc_id = table_aid, .byte_offset = 0 };
        const slot1 = SymbolicPtr{ .alloc_id = table_aid, .byte_offset = @intCast(ptr_bytes) };
        try vm.writePointerAt(slot0, ptr_align, arg0_ptr);
        try vm.writePointerAt(slot1, ptr_align, SymbolicPtr.NULL);
        sys_st.argv_alloc = table_aid;
    }
    return retPtr(.{ .alloc_id = sys_st.argv_alloc, .byte_offset = 0 });
}

// ------------------- Windows Host Dispatch --------------------

/// Dispatches a `core.sys.windows` `extern "C"` call on a Windows host (`builtin.os.tag == .windows`).
fn evalWindowsHostOp(
    vm: *MirVm,
    frame_idx: usize,
    op: ShimOp,
    call_site: mir.MirCallSite,
    ret_ty: TypeId,
    span: Span,
) VmEvalError!?RegSlot {
    if (builtin.os.tag != .windows) return null;
    const sys_st = ensureSysState(vm);
    const invalid_handle_val: usize = std.math.maxInt(usize);

    switch (op) {
        .win_get_last_error => return try retUnsigned(vm, ret_ty, sys_st.win_last_error),
        .win_set_last_error => {
            const code: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            sys_st.win_last_error = code;
            win32.SetLastError(code);
            return .{ .scalar_u64 = 0 };
        },
        .win_get_std_handle => {
            const std_id: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            return switch (std_id) {
                0xFFFF_FFF6 => retPtr(.{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = STD_IN_TOKEN }),
                0xFFFF_FFF5 => retPtr(.{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = STD_OUT_TOKEN }),
                0xFFFF_FFF4 => retPtr(.{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = STD_ERR_TOKEN }),
                else => blk: {
                    sys_st.win_last_error = 6;
                    break :blk retPtr(invalidWinHandlePtr(vm));
                },
            };
        },
        .win_exit_process => {
            const code_u32: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            vm.exited_with_code = @bitCast(code_u32);
            return error.ProcessExited;
        },
        .win_create_file_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const access: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const share: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const sec_ptr = argPtr(vm, frame_idx, call_site, 3);
            const disp: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
            var sec_buf: [24]u8 align(8) = @splat(0);
            var has_sec = false;
            if (!sec_ptr.alloc_id.isNullOrNone()) {
                try readVmWin32SecurityAttrs(vm, sec_ptr, &sec_buf);
                has_sec = true;
            }
            const res_h = win32.CreateFileW(
                path_w.ptr,
                access,
                share,
                if (has_sec) &sec_buf else null,
                disp,
                flags,
                null,
            );
            sys_st.win_last_error = win32.GetLastError();
            const raw_bits: usize = if (res_h) |ptr| @intFromPtr(ptr) else 0;
            if (raw_bits == 0 or raw_bits == invalid_handle_val) {
                return retPtr(invalidWinHandlePtr(vm));
            }
            return retPtr(try registerWinHandle(vm, .os_handle, raw_bits));
        },
        .win_nt_create_file => {
            const handle_out_ptr = argPtr(vm, frame_idx, call_site, 0);
            const access: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const oa_ptr = argPtr(vm, frame_idx, call_site, 2);
            const iosb_ptr = argPtr(vm, frame_idx, call_site, 3);
            const alloc_sz_ptr = argPtr(vm, frame_idx, call_site, 4);
            const file_attrs: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
            const share: u32 = @truncate(try argU64(vm, frame_idx, call_site, 6));
            const create_disp: u32 = @truncate(try argU64(vm, frame_idx, call_site, 7));
            const create_opts: u32 = @truncate(try argU64(vm, frame_idx, call_site, 8));

            const ptr_align = vm.options.target_layout.ptr_align_log2;
            const root_vm_h = try vm.readPointerAt(try vm.advanceSymbolicPtr(oa_ptr, 8), ptr_align);
            const us_vm_ptr = try vm.readPointerAt(try vm.advanceSymbolicPtr(oa_ptr, 16), ptr_align);
            var oa_attr_buf: [4]u8 = undefined;
            try vm.readScalarBytes(try vm.advanceSymbolicPtr(oa_ptr, 24), 0, &oa_attr_buf);
            const oa_attrs = std.mem.readInt(u32, &oa_attr_buf, .little);

            var us_hdr: [4]u8 = undefined;
            try vm.readScalarBytes(us_vm_ptr, 0, &us_hdr);
            const us_byte_len = std.mem.readInt(u16, us_hdr[0..2], .little);
            const us_buf_ptr = try vm.readPointerAt(try vm.advanceSymbolicPtr(us_vm_ptr, 8), ptr_align);
            const unit_count: usize = us_byte_len / 2;
            const host_units = vm.allocator.alloc(u16, @max(unit_count, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_units);
            if (us_byte_len > 0) {
                const raw_bytes = vm.allocator.alloc(u8, us_byte_len) catch return error.OutOfMemory;
                defer vm.allocator.free(raw_bytes);
                try vm.readScalarBytes(us_buf_ptr, 0, raw_bytes);
                for (0..unit_count) |u_i| {
                    host_units[u_i] = std.mem.readInt(u16, raw_bytes[u_i * 2 ..][0..2], .little);
                }
            }
            var host_us = ntdll.UnicodeString{
                .len = @intCast(unit_count * 2),
                .max_len = @intCast(unit_count * 2),
                .buf = host_units.ptr,
            };
            const root_os_h = if (root_vm_h.alloc_id.isNullOrNone()) null else resolveWinOsHandle(vm, root_vm_h);
            var host_oa = ntdll.ObjectAttributes{
                .len = @sizeOf(ntdll.ObjectAttributes),
                .root_dir = root_os_h,
                .obj_name = &host_us,
                .attrs = oa_attrs,
                .sec_desc = null,
                .sec_qos = null,
            };
            var host_iosb = ntdll.IoStatusBlock{ .status = 0, .info = 0 };
            var opt_alloc_sz: i64 = 0;
            var has_alloc_sz = false;
            if (!alloc_sz_ptr.alloc_id.isNullOrNone()) {
                var sz_b: [8]u8 = undefined;
                try vm.readScalarBytes(alloc_sz_ptr, 0, &sz_b);
                opt_alloc_sz = std.mem.readInt(i64, &sz_b, .little);
                has_alloc_sz = true;
            }
            var created_h: ?*anyopaque = null;
            const nt_status = ntdll.NtCreateFile(
                &created_h,
                access,
                &host_oa,
                &host_iosb,
                if (has_alloc_sz) &opt_alloc_sz else null,
                file_attrs,
                share,
                create_disp,
                create_opts,
                null,
                0,
            );
            try writeVmUsize(vm, iosb_ptr, host_iosb.status);
            try writeVmUsize(vm, try vm.advanceSymbolicPtr(iosb_ptr, vm.options.target_layout.ptr_byte_size), host_iosb.info);
            if (nt_status >= 0 and created_h != null) {
                const vm_h = try registerWinHandle(vm, .os_handle, @intFromPtr(created_h.?));
                try vm.writePointerAt(handle_out_ptr, ptr_align, vm_h);
            } else {
                try vm.writePointerAt(handle_out_ptr, ptr_align, SymbolicPtr.NULL);
            }
            return try retSigned(vm, ret_ty, nt_status);
        },
        .win_rtl_nt_status_to_dos_error => {
            const nt_status: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            return try retUnsigned(vm, ret_ty, ntdll.RtlNtStatusToDosError(nt_status));
        },
        .win_close_handle => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (h_ptr.alloc_id == vm.dangling_empty_alloc and h_ptr.byte_offset >= HANDLE_SLOT_BASE) {
                const idx: usize = h_ptr.byte_offset - HANDLE_SLOT_BASE;
                if (idx < sys_st.win_handles.items.len and sys_st.win_handles.items[idx].kind == .os_handle) {
                    const raw_bits = sys_st.win_handles.items[idx].raw_bits;
                    sys_st.win_handles.items[idx] = .{};
                    const ok = win32.CloseHandle(@ptrFromInt(raw_bits));
                    sys_st.win_last_error = win32.GetLastError();
                    return try retSigned(vm, ret_ty, ok);
                }
            }
            sys_st.win_last_error = 6;
            return try retSigned(vm, ret_ty, 0);
        },
        .win_write_file => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            const buf_ptr = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const written_out = argPtr(vm, frame_idx, call_site, 3);
            const ov_ptr = argPtr(vm, frame_idx, call_site, 4);
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;

            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            if (byte_len > 0) try vm.readScalarBytes(buf_ptr, 0, host_buf[0..byte_len]);

            if (h_ptr.alloc_id == vm.dangling_empty_alloc and
                (h_ptr.byte_offset == STD_OUT_TOKEN or h_ptr.byte_offset == STD_ERR_TOKEN))
            {
                const cap_target = if (h_ptr.byte_offset == STD_OUT_TOKEN)
                    vm.options.stdout_capture
                else
                    vm.options.stderr_capture;
                if (cap_target) |cap| {
                    if (byte_len > 0) cap.appendSlice(vm.allocator, host_buf[0..byte_len]) catch return error.OutOfMemory;
                }
                if (!written_out.alloc_id.isNullOrNone()) try writeVmU32(vm, written_out, byte_len);
                sys_st.win_last_error = 0;
                return try retSigned(vm, ret_ty, 1);
            }

            const os_h = resolveWinOsHandle(vm, h_ptr) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var ov_bytes: [32]u8 align(8) = @splat(0);
            var has_ov = false;
            if (!ov_ptr.alloc_id.isNullOrNone()) {
                try vm.readScalarBytes(ov_ptr, 0, ov_bytes[0..24]);
                has_ov = true;
            }
            var host_written: u32 = 0;
            const ok = win32.WriteFile(os_h, host_buf.ptr, byte_len, &host_written, if (has_ov) &ov_bytes else null);
            sys_st.win_last_error = win32.GetLastError();
            if (!written_out.alloc_id.isNullOrNone()) try writeVmU32(vm, written_out, host_written);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_read_file => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            const buf_out = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const read_out = argPtr(vm, frame_idx, call_site, 3);
            const ov_ptr = argPtr(vm, frame_idx, call_site, 4);
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;

            const os_h = resolveWinOsHandle(vm, h_ptr) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            var ov_bytes: [32]u8 align(8) = @splat(0);
            var has_ov = false;
            if (!ov_ptr.alloc_id.isNullOrNone()) {
                try vm.readScalarBytes(ov_ptr, 0, ov_bytes[0..24]);
                has_ov = true;
            }
            var host_read: u32 = 0;
            const ok = win32.ReadFile(os_h, host_buf.ptr, byte_len, &host_read, if (has_ov) &ov_bytes else null);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 and host_read > 0) {
                try vm.writeScalarBytes(buf_out, 0, host_buf[0..host_read]);
            }
            if (!read_out.alloc_id.isNullOrNone()) try writeVmU32(vm, read_out, host_read);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_flush_file_buffers => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const ok = win32.FlushFileBuffers(os_h);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_set_file_pointer_ex => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const dist = try argI64(vm, frame_idx, call_site, 1);
            const new_pos_ptr = argPtr(vm, frame_idx, call_site, 2);
            const method: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            var new_pos: i64 = 0;
            const ok = win32.SetFilePointerEx(os_h, dist, &new_pos, method);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 and !new_pos_ptr.alloc_id.isNullOrNone()) {
                try writeVmI64(vm, new_pos_ptr, new_pos);
            }
            return try retSigned(vm, ret_ty, ok);
        },
        .win_set_end_of_file => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const ok = win32.SetEndOfFile(os_h);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_file_info_by_handle => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            var info_buf: [52]u8 align(8) = @splat(0);
            const ok = win32.GetFileInformationByHandle(os_h, &info_buf);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try vm.writeScalarBytes(out_ptr, 0, &info_buf);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_file_info_by_handle_ex => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const cls: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const out_ptr = argPtr(vm, frame_idx, call_site, 2);
            const buf_bytes: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            if (buf_bytes > 65_536) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(buf_bytes, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            @memset(host_buf, 0);
            const ok = win32.GetFileInformationByHandleEx(os_h, cls, host_buf.ptr, buf_bytes);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 and buf_bytes > 0) try vm.writeScalarBytes(out_ptr, 0, host_buf[0..buf_bytes]);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_set_file_info_by_handle => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const cls: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const in_ptr = argPtr(vm, frame_idx, call_site, 2);
            const buf_bytes: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            if (buf_bytes > 131_072) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(buf_bytes, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            @memset(host_buf, 0);
            if ((cls == 3 or cls == 22) and buf_bytes >= 20) {
                try vm.readScalarBytes(in_ptr, 0, host_buf[0..4]);
                const root_vm_h = try vm.readPointerAt(
                    try vm.advanceSymbolicPtr(in_ptr, 8),
                    vm.options.target_layout.ptr_align_log2,
                );
                const root_bits: usize = if (root_vm_h.alloc_id.isNullOrNone())
                    0
                else if (resolveWinOsHandle(vm, root_vm_h)) |rh|
                    @intFromPtr(rh)
                else
                    0;
                std.mem.writeInt(usize, host_buf[8..16], root_bits, .little);
                try vm.readScalarBytes(try vm.advanceSymbolicPtr(in_ptr, 16), 0, host_buf[16..20]);
                const name_bytes = @min(std.mem.readInt(u32, host_buf[16..20], .little), buf_bytes - 20);
                if (name_bytes > 0) {
                    try vm.readScalarBytes(try vm.advanceSymbolicPtr(in_ptr, 20), 0, host_buf[20 .. 20 + name_bytes]);
                }
            } else if (cls == 0 and buf_bytes >= 36) {
                try vm.readScalarBytes(in_ptr, 0, host_buf[0..36]);
            } else if (buf_bytes > 0) {
                try vm.readScalarBytes(in_ptr, 0, host_buf[0..buf_bytes]);
            }
            const ok = win32.SetFileInformationByHandle(os_h, cls, host_buf.ptr, buf_bytes);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_file_attributes_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const attrs = win32.GetFileAttributesW(path_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            return try retUnsigned(vm, ret_ty, attrs);
        },
        .win_set_file_attributes_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const attrs: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const ok = win32.SetFileAttributesW(path_w.ptr, attrs);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_file_attributes_ex_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const lvl: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const out_ptr = argPtr(vm, frame_idx, call_site, 2);
            var attr_data: [36]u8 align(4) = @splat(0);
            const ok = win32.GetFileAttributesExW(path_w.ptr, lvl, &attr_data);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try vm.writeScalarBytes(out_ptr, 0, &attr_data);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_final_path_name_w => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retUnsigned(vm, ret_ty, 0);
            };
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            const host_w = vm.allocator.alloc(u16, @max(cap_w, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetFinalPathNameByHandleW(os_h, host_w.ptr, cap_w, flags);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w and !out_ptr.alloc_id.isNullOrNone()) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_get_full_path_name_w => {
            const name_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(name_w);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const out_ptr = argPtr(vm, frame_idx, call_site, 2);
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            const host_w = vm.allocator.alloc(u16, @max(cap_w, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetFullPathNameW(name_w.ptr, cap_w, host_w.ptr, null);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w and !out_ptr.alloc_id.isNullOrNone()) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_move_file_ex_w => {
            const src_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(src_w);
            const dst_ptr = argPtr(vm, frame_idx, call_site, 1);
            const dst_w = if (dst_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, dst_ptr);
            defer if (dst_w) |dw| vm.allocator.free(dw);
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const ok = win32.MoveFileExW(src_w.ptr, if (dst_w) |dw| dw.ptr else null, flags);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_replace_file_w => {
            const rep_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(rep_w);
            const src_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(src_w);
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const ok = win32.ReplaceFileW(rep_w.ptr, src_w.ptr, null, flags, null, null);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_delete_file_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const ok = win32.DeleteFileW(path_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_create_directory_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const ok = win32.CreateDirectoryW(path_w.ptr, null);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_remove_directory_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const ok = win32.RemoveDirectoryW(path_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_create_hard_link_w => {
            const new_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(new_w);
            const old_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(old_w);
            const ok = win32.CreateHardLinkW(new_w.ptr, old_w.ptr, null);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_device_io_control => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const ctl_code: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const in_ptr = argPtr(vm, frame_idx, call_site, 2);
            const in_bytes: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const out_ptr = argPtr(vm, frame_idx, call_site, 4);
            const out_bytes: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
            const ret_ptr = argPtr(vm, frame_idx, call_site, 6);
            if (in_bytes > 65_536 or out_bytes > 65_536) return error.ResourceLimitExceeded;

            const host_in = vm.allocator.alloc(u8, @max(in_bytes, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_in);
            if (!in_ptr.alloc_id.isNullOrNone() and in_bytes > 0) {
                try vm.readScalarBytes(in_ptr, 0, host_in[0..in_bytes]);
                if (ctl_code == 0x0009_8344 and in_bytes >= 32) {
                    const src_vm_h = try vm.readPointerAt(in_ptr, vm.options.target_layout.ptr_align_log2);
                    const src_bits: usize = if (resolveWinOsHandle(vm, src_vm_h)) |sh| @intFromPtr(sh) else 0;
                    std.mem.writeInt(usize, host_in[0..8], src_bits, .little);
                }
            }
            const host_out = vm.allocator.alloc(u8, @max(out_bytes, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_out);
            var ret_count: u32 = 0;
            const ok = win32.DeviceIoControl(
                os_h,
                ctl_code,
                if (in_ptr.alloc_id.isNullOrNone()) null else host_in.ptr,
                in_bytes,
                if (out_ptr.alloc_id.isNullOrNone()) null else host_out.ptr,
                out_bytes,
                &ret_count,
                null,
            );
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 and !out_ptr.alloc_id.isNullOrNone() and ret_count > 0 and ret_count <= out_bytes) {
                try vm.writeScalarBytes(out_ptr, 0, host_out[0..ret_count]);
            }
            if (!ret_ptr.alloc_id.isNullOrNone()) try writeVmU32(vm, ret_ptr, ret_count);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_find_first_file_ex_w => {
            const pat_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(pat_w);
            const info_lvl: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const data_out = argPtr(vm, frame_idx, call_site, 2);
            const search_op: i32 = @truncate(try argI64(vm, frame_idx, call_site, 3));
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
            var find_buf: [592]u8 align(4) = @splat(0);
            const find_h = win32.FindFirstFileExW(pat_w.ptr, info_lvl, &find_buf, search_op, null, flags);
            sys_st.win_last_error = win32.GetLastError();
            const raw_bits: usize = if (find_h) |fh| @intFromPtr(fh) else 0;
            if (raw_bits == 0 or raw_bits == invalid_handle_val) return retPtr(invalidWinHandlePtr(vm));
            try vm.writeScalarBytes(data_out, 0, &find_buf);
            return retPtr(try registerWinHandle(vm, .find_handle, raw_bits));
        },
        .win_find_next_file_w => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            const data_out = argPtr(vm, frame_idx, call_site, 1);
            const raw_bits = resolveRawWinHandleOpt(sys_st, h_ptr.byte_offset, .find_handle) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var find_buf: [592]u8 align(4) = @splat(0);
            const ok = win32.FindNextFileW(@ptrFromInt(raw_bits), &find_buf);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try vm.writeScalarBytes(data_out, 0, &find_buf);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_find_close => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (h_ptr.alloc_id == vm.dangling_empty_alloc and h_ptr.byte_offset >= HANDLE_SLOT_BASE) {
                const idx: usize = h_ptr.byte_offset - HANDLE_SLOT_BASE;
                if (idx < sys_st.win_handles.items.len and sys_st.win_handles.items[idx].kind == .find_handle) {
                    const raw_bits = sys_st.win_handles.items[idx].raw_bits;
                    sys_st.win_handles.items[idx] = .{};
                    const ok = win32.FindClose(@ptrFromInt(raw_bits));
                    sys_st.win_last_error = win32.GetLastError();
                    return try retSigned(vm, ret_ty, ok);
                }
            }
            sys_st.win_last_error = 6;
            return try retSigned(vm, ret_ty, 0);
        },
        .win_create_file_mapping_w => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return retPtr(SymbolicPtr.NULL);
            };
            const prot: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const max_hi: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const max_lo: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
            const map_h = win32.CreateFileMappingW(os_h, null, prot, max_hi, max_lo, null);
            sys_st.win_last_error = win32.GetLastError();
            if (map_h == null) return retPtr(SymbolicPtr.NULL);
            return retPtr(try registerWinHandle(vm, .os_handle, @intFromPtr(map_h.?)));
        },
        .win_map_view_of_file => {
            const map_os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return retPtr(SymbolicPtr.NULL);
            };
            const access: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const off_hi: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const off_lo: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const map_bytes: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
            if (map_bytes > vm.options.mem_limit) return error.ResourceLimitExceeded;
            const host_view = win32.MapViewOfFile(map_os_h, access, off_hi, off_lo, map_bytes);
            sys_st.win_last_error = win32.GetLastError();
            if (host_view == null) return retPtr(SymbolicPtr.NULL);
            const is_mut = (access & 0x0002) != 0;
            const alloc_bytes = if (is_mut)
                @max(map_bytes, 1)
            else
                std.mem.alignForward(usize, @max(map_bytes, 1), 4096);
            if (alloc_bytes > vm.options.mem_limit) {
                _ = win32.UnmapViewOfFile(host_view.?);
                return error.ResourceLimitExceeded;
            }
            const vm_aid = try vm.allocMemory(alloc_bytes, 4, is_mut, false, !is_mut, 0, span);
            const vm_base = SymbolicPtr{ .alloc_id = vm_aid, .byte_offset = 0 };
            if (map_bytes > 0) {
                if (is_mut) {
                    try vm.writeScalarBytes(vm_base, 0, host_view.?[0..map_bytes]);
                } else {
                    const alloc_rec = &vm.allocations.items[vm_aid.payloadIndex()];
                    @memcpy(alloc_rec.bytes[0..map_bytes], host_view.?[0..map_bytes]);
                    @memset(alloc_rec.init_mask, std.math.maxInt(u64));
                }
            } else if (!is_mut) {
                @memset(vm.allocations.items[vm_aid.payloadIndex()].init_mask, std.math.maxInt(u64));
            }
            sys_st.mapped_views.append(vm.allocator, .{
                .vm_alloc = vm_aid,
                .host_addr = @intFromPtr(host_view.?),
                .byte_len = map_bytes,
            }) catch return error.OutOfMemory;
            return retPtr(vm_base);
        },
        .win_unmap_view_of_file => {
            const view_ptr = argPtr(vm, frame_idx, call_site, 0);
            for (sys_st.mapped_views.items, 0..) |rec, idx| {
                if (rec.vm_alloc == view_ptr.alloc_id and view_ptr.byte_offset == 0) {
                    const ok = win32.UnmapViewOfFile(@ptrFromInt(rec.host_addr));
                    sys_st.win_last_error = win32.GetLastError();
                    vm.allocations.items[rec.vm_alloc.payloadIndex()].is_live = false;
                    _ = sys_st.mapped_views.swapRemove(idx);
                    return try retSigned(vm, ret_ty, ok);
                }
            }
            sys_st.win_last_error = 87;
            return try retSigned(vm, ret_ty, 0);
        },
        .win_lock_file_ex => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const lo: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const hi: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
            const ov_ptr = argPtr(vm, frame_idx, call_site, 5);
            var ov_buf: [32]u8 align(8) = @splat(0);
            try vm.readScalarBytes(ov_ptr, 0, ov_buf[0..24]);
            const ok = win32.LockFileEx(os_h, flags, 0, lo, hi, &ov_buf);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_unlock_file_ex => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const lo: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const hi: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const ov_ptr = argPtr(vm, frame_idx, call_site, 4);
            var ov_buf: [32]u8 align(8) = @splat(0);
            try vm.readScalarBytes(ov_ptr, 0, ov_buf[0..24]);
            const ok = win32.UnlockFileEx(os_h, 0, lo, hi, &ov_buf);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_create_event_w => {
            const manual: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const init_st: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            const ev_h = win32.CreateEventW(null, manual, init_st, null);
            sys_st.win_last_error = win32.GetLastError();
            if (ev_h == null) return retPtr(SymbolicPtr.NULL);
            return retPtr(try registerWinHandle(vm, .os_handle, @intFromPtr(ev_h.?)));
        },
        .win_wait_for_single_object => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retUnsigned(vm, ret_ty, 0xFFFF_FFFF);
            };
            const timeout_ms: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const res = win32.WaitForSingleObject(os_h, timeout_ms);
            sys_st.win_last_error = win32.GetLastError();
            return try retUnsigned(vm, ret_ty, res);
        },
        .win_read_directory_changes_w => {
            const dir_vm_h = argPtr(vm, frame_idx, call_site, 0);
            const os_dir_h = resolveWinOsHandle(vm, dir_vm_h) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const notify_out = argPtr(vm, frame_idx, call_site, 1);
            const notify_cap: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const subtree: i32 = @truncate(try argI64(vm, frame_idx, call_site, 3));
            const filter: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
            const ret_out = argPtr(vm, frame_idx, call_site, 5);
            const ov_ptr = argPtr(vm, frame_idx, call_site, 6);
            if (notify_cap > 1_048_576) return error.ResourceLimitExceeded;

            if (ov_ptr.alloc_id.isNullOrNone()) {
                const sync_buf = vm.allocator.alloc(u8, @max(notify_cap, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(sync_buf);
                var sync_ret: u32 = 0;
                const ok = win32.ReadDirectoryChangesW(os_dir_h, sync_buf.ptr, notify_cap, subtree, filter, &sync_ret, null, null);
                sys_st.win_last_error = win32.GetLastError();
                if (ok != 0 and sync_ret > 0) try vm.writeScalarBytes(notify_out, 0, sync_buf[0..sync_ret]);
                if (!ret_out.alloc_id.isNullOrNone()) try writeVmU32(vm, ret_out, sync_ret);
                return try retSigned(vm, ret_ty, ok);
            }

            const ev_vm_h = try vm.readPointerAt(
                try vm.advanceSymbolicPtr(ov_ptr, 24),
                vm.options.target_layout.ptr_align_log2,
            );
            const host_ev = if (ev_vm_h.alloc_id.isNullOrNone()) null else resolveWinOsHandle(vm, ev_vm_h);
            const host_buf = vm.allocator.alloc(u8, @max(notify_cap, 1)) catch return error.OutOfMemory;
            errdefer vm.allocator.free(host_buf);
            const host_ov = vm.allocator.create([4]usize) catch return error.OutOfMemory;
            errdefer vm.allocator.destroy(host_ov);
            host_ov.* = .{ 0, 0, 0, if (host_ev) |eh| @intFromPtr(eh) else 0 };

            const ok = win32.ReadDirectoryChangesW(os_dir_h, host_buf.ptr, notify_cap, subtree, filter, null, host_ov, null);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 or sys_st.win_last_error == 997) {
                sys_st.win_watches.append(vm.allocator, .{
                    .dir_token = dir_vm_h.byte_offset,
                    .vm_notify_buf = notify_out,
                    .vm_overlapped = ov_ptr,
                    .host_buf = host_buf,
                    .host_overlapped = host_ov,
                }) catch return error.OutOfMemory;
                return try retSigned(vm, ret_ty, ok);
            }
            vm.allocator.free(host_buf);
            vm.allocator.destroy(host_ov);
            return try retSigned(vm, ret_ty, 0);
        },
        .win_get_overlapped_result => {
            const dir_vm_h = argPtr(vm, frame_idx, call_site, 0);
            const os_h = resolveWinOsHandle(vm, dir_vm_h) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const ov_ptr = argPtr(vm, frame_idx, call_site, 1);
            const xfer_out = argPtr(vm, frame_idx, call_site, 2);
            const wait_flag: i32 = @truncate(try argI64(vm, frame_idx, call_site, 3));
            for (sys_st.win_watches.items, 0..) |watch_rec, w_i| {
                if (watch_rec.dir_token == dir_vm_h.byte_offset and
                    watch_rec.vm_overlapped.alloc_id == ov_ptr.alloc_id and
                    watch_rec.vm_overlapped.byte_offset == ov_ptr.byte_offset)
                {
                    var xfer: u32 = 0;
                    const ok = win32.GetOverlappedResult(os_h, watch_rec.host_overlapped, &xfer, wait_flag);
                    sys_st.win_last_error = win32.GetLastError();
                    if (ok != 0) {
                        if (xfer > 0 and xfer <= watch_rec.host_buf.len) {
                            try vm.writeScalarBytes(watch_rec.vm_notify_buf, 0, watch_rec.host_buf[0..xfer]);
                        }
                        try writeVmU32(vm, xfer_out, xfer);
                        vm.allocator.free(watch_rec.host_buf);
                        vm.allocator.destroy(watch_rec.host_overlapped);
                        _ = sys_st.win_watches.swapRemove(w_i);
                    }
                    return try retSigned(vm, ret_ty, ok);
                }
            }
            sys_st.win_last_error = 87;
            return try retSigned(vm, ret_ty, 0);
        },
        .win_cancel_io_ex => {
            const dir_vm_h = argPtr(vm, frame_idx, call_site, 0);
            const os_h = resolveWinOsHandle(vm, dir_vm_h) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var idx: usize = 0;
            while (idx < sys_st.win_watches.items.len) {
                const watch_rec = sys_st.win_watches.items[idx];
                if (watch_rec.dir_token == dir_vm_h.byte_offset) {
                    _ = win32.CancelIoEx(os_h, watch_rec.host_overlapped);
                    vm.allocator.free(watch_rec.host_buf);
                    vm.allocator.destroy(watch_rec.host_overlapped);
                    _ = sys_st.win_watches.swapRemove(idx);
                } else {
                    idx += 1;
                }
            }
            const ok = win32.CancelIoEx(os_h, null);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_console_mode => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (h_ptr.alloc_id == vm.dangling_empty_alloc and
                (h_ptr.byte_offset == STD_OUT_TOKEN or h_ptr.byte_offset == STD_ERR_TOKEN or h_ptr.byte_offset == STD_IN_TOKEN))
            {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            }
            const os_h = resolveWinOsHandle(vm, h_ptr) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var mode: u32 = 0;
            const ok = win32.GetConsoleMode(os_h, &mode);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try writeVmU32(vm, argPtr(vm, frame_idx, call_site, 1), mode);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_file_type => {
            const h_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (h_ptr.alloc_id == vm.dangling_empty_alloc and
                (h_ptr.byte_offset == STD_OUT_TOKEN or h_ptr.byte_offset == STD_ERR_TOKEN or h_ptr.byte_offset == STD_IN_TOKEN))
            {
                return try retUnsigned(vm, ret_ty, 0x0003);
            }
            const os_h = resolveWinOsHandle(vm, h_ptr) orelse return try retUnsigned(vm, ret_ty, 0);
            return try retUnsigned(vm, ret_ty, win32.GetFileType(os_h));
        },
        .win_query_performance_counter => {
            var counter: i64 = 0;
            const ok = win32.QueryPerformanceCounter(&counter);
            try writeVmI64(vm, argPtr(vm, frame_idx, call_site, 0), counter);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_query_performance_frequency => {
            var freq: i64 = 0;
            const ok = win32.QueryPerformanceFrequency(&freq);
            try writeVmI64(vm, argPtr(vm, frame_idx, call_site, 0), freq);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_system_time_precise => {
            var ft: [2]u32 = .{ 0, 0 };
            win32.GetSystemTimePreciseAsFileTime(&ft);
            var buf: [8]u8 = undefined;
            std.mem.writeInt(u32, buf[0..4], ft[0], .little);
            std.mem.writeInt(u32, buf[4..8], ft[1], .little);
            try vm.writeScalarBytes(argPtr(vm, frame_idx, call_site, 0), 0, &buf);
            return .{ .scalar_u64 = 0 };
        },
        .win_sleep => {
            const ms: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            win32.Sleep(ms);
            return .{ .scalar_u64 = 0 };
        },
        .win_get_command_line_w => {
            if (sys_st.cmdline_w_alloc == .none) {
                const units = [_]u16{ 'c', 'o', 'r', 'e', 'x', '_', 'o', 'r', 'a', 'c', 'l', 'e', 0 };
                const aid = try vm.allocMemory(units.len * 2, 1, false, false, false, 0, span);
                sys_st.cmdline_w_alloc = aid;
                const rec = &vm.allocations.items[aid.payloadIndex()];
                for (units, 0..) |unit, u_i| {
                    std.mem.writeInt(u16, rec.bytes[u_i * 2 ..][0..2], unit, .little);
                }
                @memset(rec.init_mask, std.math.maxInt(u64));
            }
            return retPtr(.{ .alloc_id = sys_st.cmdline_w_alloc, .byte_offset = 0 });
        },
        .win_get_environment_strings_w => {
            const raw_env = win32.GetEnvironmentStringsW() orelse return retPtr(SymbolicPtr.NULL);
            defer _ = win32.FreeEnvironmentStringsW(raw_env);
            var len_units: usize = 0;
            while (len_units + 1 < 1_048_576) : (len_units += 1) {
                if (raw_env[len_units] == 0 and raw_env[len_units + 1] == 0) {
                    len_units += 2;
                    break;
                }
            }
            const aid = try vm.allocMemory(len_units * 2, 1, true, false, false, 0, span);
            const out_ptr = SymbolicPtr{ .alloc_id = aid, .byte_offset = 0 };
            try writeVmWideUnits(vm, out_ptr, raw_env[0..len_units]);
            return retPtr(out_ptr);
        },
        .win_free_environment_strings_w => {
            const env_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (env_ptr.alloc_id.domain() == .vm_alloc and env_ptr.byte_offset == 0) {
                vm.allocations.items[env_ptr.alloc_id.payloadIndex()].is_live = false;
            }
            return try retSigned(vm, ret_ty, 1);
        },
        .win_get_environment_variable_w => {
            const key_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(key_w);
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            if (cap_w > 65_536) return error.ResourceLimitExceeded;
            if (out_ptr.alloc_id.isNullOrNone() or cap_w == 0) {
                const req = win32.GetEnvironmentVariableW(key_w.ptr, null, 0);
                sys_st.win_last_error = win32.GetLastError();
                return try retUnsigned(vm, ret_ty, req);
            }
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetEnvironmentVariableW(key_w.ptr, host_w.ptr, cap_w);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_set_environment_variable_w => {
            const key_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(key_w);
            const val_ptr = argPtr(vm, frame_idx, call_site, 1);
            const val_w = if (val_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, val_ptr);
            defer if (val_w) |vw| vm.allocator.free(vw);
            const ok = win32.SetEnvironmentVariableW(key_w.ptr, if (val_w) |vw| vw.ptr else null);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_expand_environment_strings_w => {
            const src_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(src_w);
            const dst_ptr = argPtr(vm, frame_idx, call_site, 1);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            if (dst_ptr.alloc_id.isNullOrNone() or cap_w == 0) {
                const req = win32.ExpandEnvironmentStringsW(src_w.ptr, null, 0);
                sys_st.win_last_error = win32.GetLastError();
                return try retUnsigned(vm, ret_ty, req);
            }
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.ExpandEnvironmentStringsW(src_w.ptr, host_w.ptr, cap_w);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len <= cap_w) {
                try writeVmWideUnits(vm, dst_ptr, host_w[0..res_len]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_get_current_directory_w => {
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            if (out_ptr.alloc_id.isNullOrNone() or cap_w == 0) {
                const req = win32.GetCurrentDirectoryW(0, null);
                sys_st.win_last_error = win32.GetLastError();
                return try retUnsigned(vm, ret_ty, req);
            }
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetCurrentDirectoryW(cap_w, host_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_set_current_directory_w => {
            const path_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_w);
            const ok = win32.SetCurrentDirectoryW(path_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_module_file_name_w => {
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            if (cap_w == 0 or cap_w > MAX_SHIM_PATH_UNITS) return try retUnsigned(vm, ret_ty, 0);
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetModuleFileNameW(null, host_w.ptr, cap_w);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0) {
                const write_cnt = @min(res_len + 1, cap_w);
                try writeVmWideUnits(vm, out_ptr, host_w[0..write_cnt]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_get_temp_path_w => {
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            if (out_ptr.alloc_id.isNullOrNone() or cap_w == 0) {
                const req = win32.GetTempPathW(0, null);
                sys_st.win_last_error = win32.GetLastError();
                return try retUnsigned(vm, ret_ty, req);
            }
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.GetTempPathW(cap_w, host_w.ptr);
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_get_module_handle_w => {
            const name_ptr = argPtr(vm, frame_idx, call_site, 0);
            const name_w = if (name_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, name_ptr);
            defer if (name_w) |nw| vm.allocator.free(nw);
            const mod_h = win32.GetModuleHandleW(if (name_w) |nw| nw.ptr else null);
            sys_st.win_last_error = win32.GetLastError();
            if (mod_h == null) return retPtr(SymbolicPtr.NULL);
            return retPtr(try registerWinHandle(vm, .module_handle, @intFromPtr(mod_h.?)));
        },
        .win_get_proc_address => {
            const mod_ptr = argPtr(vm, frame_idx, call_site, 0);
            const mod_bits = resolveRawWinHandleOpt(sys_st, mod_ptr.byte_offset, .module_handle) orelse {
                sys_st.win_last_error = 6;
                return retPtr(SymbolicPtr.NULL);
            };
            const proc_name = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(proc_name);
            const proc_addr = win32.GetProcAddress(@ptrFromInt(mod_bits), proc_name.ptr);
            sys_st.win_last_error = win32.GetLastError();
            if (proc_addr == null) return retPtr(SymbolicPtr.NULL);
            return retPtr(.{ .alloc_id = vm.dangling_empty_alloc, .byte_offset = 0x0003_0001 });
        },
        .win_get_current_process_id => {
            return try retUnsigned(vm, ret_ty, win32.GetCurrentProcessId());
        },
        .win_create_pipe => {
            const rd_out = argPtr(vm, frame_idx, call_site, 0);
            const wr_out = argPtr(vm, frame_idx, call_site, 1);
            const sec_ptr = argPtr(vm, frame_idx, call_site, 2);
            const sz_hint: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            var sec_buf: [24]u8 align(8) = @splat(0);
            var has_sec = false;
            if (!sec_ptr.alloc_id.isNullOrNone()) {
                try readVmWin32SecurityAttrs(vm, sec_ptr, &sec_buf);
                has_sec = true;
            }
            var rd_h: ?*anyopaque = null;
            var wr_h: ?*anyopaque = null;
            const ok = win32.CreatePipe(&rd_h, &wr_h, if (has_sec) &sec_buf else null, sz_hint);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0 and rd_h != null and wr_h != null) {
                const ptr_align = vm.options.target_layout.ptr_align_log2;
                try vm.writePointerAt(rd_out, ptr_align, try registerWinHandle(vm, .os_handle, @intFromPtr(rd_h.?)));
                try vm.writePointerAt(wr_out, ptr_align, try registerWinHandle(vm, .os_handle, @intFromPtr(wr_h.?)));
            }
            return try retSigned(vm, ret_ty, ok);
        },
        .win_set_handle_information => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const mask: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const ok = win32.SetHandleInformation(os_h, mask, flags);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_handle_information => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var out_flags: u32 = 0;
            const ok = win32.GetHandleInformation(os_h, &out_flags);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try writeVmU32(vm, argPtr(vm, frame_idx, call_site, 1), out_flags);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_search_path_w => {
            const dirs_ptr = argPtr(vm, frame_idx, call_site, 0);
            const dirs_w = if (dirs_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, dirs_ptr);
            defer if (dirs_w) |dw| vm.allocator.free(dw);
            const file_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(file_w);
            const ext_ptr = argPtr(vm, frame_idx, call_site, 2);
            const ext_w = if (ext_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, ext_ptr);
            defer if (ext_w) |ew| vm.allocator.free(ew);
            const cap_w: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const out_ptr = argPtr(vm, frame_idx, call_site, 4);
            if (cap_w > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            if (out_ptr.alloc_id.isNullOrNone() or cap_w == 0) {
                const req = win32.SearchPathW(
                    if (dirs_w) |dw| dw.ptr else null,
                    file_w.ptr,
                    if (ext_w) |ew| ew.ptr else null,
                    0,
                    null,
                    null,
                );
                sys_st.win_last_error = win32.GetLastError();
                return try retUnsigned(vm, ret_ty, req);
            }
            const host_w = vm.allocator.alloc(u16, cap_w) catch return error.OutOfMemory;
            defer vm.allocator.free(host_w);
            const res_len = win32.SearchPathW(
                if (dirs_w) |dw| dw.ptr else null,
                file_w.ptr,
                if (ext_w) |ew| ew.ptr else null,
                cap_w,
                host_w.ptr,
                null,
            );
            sys_st.win_last_error = win32.GetLastError();
            if (res_len > 0 and res_len < cap_w) {
                try writeVmWideUnits(vm, out_ptr, host_w[0 .. res_len + 1]);
            }
            return try retUnsigned(vm, ret_ty, res_len);
        },
        .win_init_proc_thread_attr_list => {
            const list_ptr = argPtr(vm, frame_idx, call_site, 0);
            const cnt: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const sz_ptr = argPtr(vm, frame_idx, call_site, 3);
            var host_sz: usize = @intCast(try readVmUsize(vm, sz_ptr));
            if (list_ptr.alloc_id.isNullOrNone()) {
                _ = win32.InitializeProcThreadAttributeList(null, cnt, 0, &host_sz);
                sys_st.win_last_error = win32.GetLastError();
                try writeVmUsize(vm, sz_ptr, host_sz);
                return try retSigned(vm, ret_ty, 0);
            }
            const vaddr = try vm.ptrToVirtualAddr(list_ptr, 3);
            const host_buf = vm.allocator.alignedAlloc(u8, .@"8", @max(host_sz + 64, 128)) catch return error.OutOfMemory;
            var actual_sz: usize = host_buf.len;
            const ok = win32.InitializeProcThreadAttributeList(host_buf.ptr, cnt, 0, &actual_sz);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) {
                sys_st.win_proc_attrs.put(vm.allocator, vaddr, host_buf) catch {
                    vm.allocator.free(host_buf);
                    return error.OutOfMemory;
                };
            } else {
                vm.allocator.free(host_buf);
            }
            return try retSigned(vm, ret_ty, ok);
        },
        .win_update_proc_thread_attr => {
            const list_ptr = argPtr(vm, frame_idx, call_site, 0);
            const vaddr = try vm.ptrToVirtualAddr(list_ptr, 3);
            const host_attr_buf = sys_st.win_proc_attrs.get(vaddr) orelse {
                sys_st.win_last_error = 87;
                return try retSigned(vm, ret_ty, 0);
            };
            const attr_key: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
            const val_ptr = argPtr(vm, frame_idx, call_site, 3);
            const val_bytes: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
            if (attr_key == 0x0002_0002 and val_bytes <= 64 and (val_bytes % @sizeOf(usize)) == 0) {
                const handle_cnt = val_bytes / @sizeOf(usize);
                const tail_slice = host_attr_buf[host_attr_buf.len - 64 ..];
                var h_i: usize = 0;
                while (h_i < handle_cnt) : (h_i += 1) {
                    const elem_ptr = try vm.advanceSymbolicPtr(val_ptr, @intCast(h_i * @sizeOf(usize)));
                    const vm_h = try vm.readPointerAt(elem_ptr, vm.options.target_layout.ptr_align_log2);
                    const raw_h: usize = if (resolveWinOsHandle(vm, vm_h)) |oh| @intFromPtr(oh) else 0;
                    std.mem.writeInt(usize, tail_slice[h_i * 8 ..][0..8], raw_h, .little);
                }
                const ok = win32.UpdateProcThreadAttribute(
                    host_attr_buf.ptr,
                    0,
                    attr_key,
                    tail_slice.ptr,
                    val_bytes,
                    null,
                    null,
                );
                sys_st.win_last_error = win32.GetLastError();
                return try retSigned(vm, ret_ty, ok);
            }
            sys_st.win_last_error = 87;
            return try retSigned(vm, ret_ty, 0);
        },
        .win_delete_proc_thread_attr_list => {
            const list_ptr = argPtr(vm, frame_idx, call_site, 0);
            const vaddr = try vm.ptrToVirtualAddr(list_ptr, 3);
            if (sys_st.win_proc_attrs.fetchRemove(vaddr)) |kv| {
                win32.DeleteProcThreadAttributeList(kv.value.ptr);
                vm.allocator.free(kv.value);
            }
            return .{ .scalar_u64 = 0 };
        },
        .win_create_process_w => {
            const app_ptr = argPtr(vm, frame_idx, call_site, 0);
            const app_w = if (app_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, app_ptr);
            defer if (app_w) |aw| vm.allocator.free(aw);
            const cmd_ptr = argPtr(vm, frame_idx, call_site, 1);
            const cmd_w = if (cmd_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, cmd_ptr);
            defer if (cmd_w) |cw| vm.allocator.free(cw);
            const inherit: i32 = @truncate(try argI64(vm, frame_idx, call_site, 4));
            const create_flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
            const env_ptr = argPtr(vm, frame_idx, call_site, 6);
            const env_w = if (env_ptr.alloc_id.isNullOrNone()) null else try readVmWideEnvBlock(vm, env_ptr);
            defer if (env_w) |ew| vm.allocator.free(ew);
            const cwd_ptr = argPtr(vm, frame_idx, call_site, 7);
            const cwd_w = if (cwd_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, cwd_ptr);
            defer if (cwd_w) |dw| vm.allocator.free(dw);
            const si_ptr = argPtr(vm, frame_idx, call_site, 8);
            const pi_out = argPtr(vm, frame_idx, call_site, 9);

            var si_buf: [112]u8 align(8) = @splat(0);
            var cb_b: [4]u8 = undefined;
            try vm.readScalarBytes(si_ptr, 0, &cb_b);
            const si_bytes = @min(@as(usize, std.mem.readInt(u32, &cb_b, .little)), 112);
            std.mem.writeInt(u32, si_buf[0..4], @intCast(si_bytes), .little);
            var flags_b: [4]u8 = undefined;
            try vm.readScalarBytes(try vm.advanceSymbolicPtr(si_ptr, 60), 0, &flags_b);
            const si_flags = std.mem.readInt(u32, &flags_b, .little);
            std.mem.writeInt(u32, si_buf[60..64], si_flags, .little);
            const ptr_align = vm.options.target_layout.ptr_align_log2;
            if ((si_flags & 0x0000_0100) != 0) {
                inline for ([_]usize{ 80, 88, 96 }) |h_off| {
                    const vm_std_h = try vm.readPointerAt(try vm.advanceSymbolicPtr(si_ptr, h_off), ptr_align);
                    const raw_std_h: usize = if (resolveWinOsHandle(vm, vm_std_h)) |oh| @intFromPtr(oh) else 0;
                    std.mem.writeInt(usize, si_buf[h_off..][0..8], raw_std_h, .little);
                }
            }
            if ((create_flags & 0x0008_0000) != 0 and si_bytes >= 112) {
                const attr_vm_ptr = try vm.readPointerAt(try vm.advanceSymbolicPtr(si_ptr, 104), ptr_align);
                const attr_vaddr = try vm.ptrToVirtualAddr(attr_vm_ptr, 3);
                if (sys_st.win_proc_attrs.get(attr_vaddr)) |host_attr| {
                    std.mem.writeInt(usize, si_buf[104..112], @intFromPtr(host_attr.ptr), .little);
                }
            }
            const eff_create_flags: u32 = if (env_w != null)
                (create_flags | 0x0000_0400)
            else
                (create_flags & ~@as(u32, 0x0000_0400));
            var host_pi: [4]usize = .{ 0, 0, 0, 0 };
            const ok = win32.CreateProcessW(
                if (app_w) |aw| aw.ptr else null,
                if (cmd_w) |cw| cw.ptr else null,
                null,
                null,
                inherit,
                eff_create_flags,
                if (env_w) |ew| @ptrCast(ew.ptr) else null,
                if (cwd_w) |dw| dw.ptr else null,
                &si_buf,
                &host_pi,
            );
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) {
                const vm_proc_h = try registerWinHandle(vm, .os_handle, host_pi[0]);
                const vm_thrd_h = try registerWinHandle(vm, .os_handle, host_pi[1]);
                try vm.writePointerAt(pi_out, ptr_align, vm_proc_h);
                try vm.writePointerAt(try vm.advanceSymbolicPtr(pi_out, 8), ptr_align, vm_thrd_h);
                const ids_raw = host_pi[2];
                try writeVmU32(vm, try vm.advanceSymbolicPtr(pi_out, 16), @truncate(ids_raw));
                try writeVmU32(vm, try vm.advanceSymbolicPtr(pi_out, 20), @truncate(ids_raw >> 32));
            }
            return try retSigned(vm, ret_ty, ok);
        },
        .win_get_exit_code_process => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            var exit_code: u32 = 0;
            const ok = win32.GetExitCodeProcess(os_h, &exit_code);
            sys_st.win_last_error = win32.GetLastError();
            if (ok != 0) try writeVmU32(vm, argPtr(vm, frame_idx, call_site, 1), exit_code);
            return try retSigned(vm, ret_ty, ok);
        },
        .win_terminate_process => {
            const os_h = resolveWinOsHandle(vm, argPtr(vm, frame_idx, call_site, 0)) orelse {
                sys_st.win_last_error = 6;
                return try retSigned(vm, ret_ty, 0);
            };
            const code: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const ok = win32.TerminateProcess(os_h, code);
            sys_st.win_last_error = win32.GetLastError();
            return try retSigned(vm, ret_ty, ok);
        },
        .win_reg_open_key_ex_w => {
            const root_ptr = argPtr(vm, frame_idx, call_site, 0);
            const root_bits: usize = if (root_ptr.alloc_id == vm.dangling_empty_alloc and
                root_ptr.byte_offset >= 0x8000_0000 and root_ptr.byte_offset <= 0x8000_000F)
                @as(usize, @bitCast(@as(isize, @as(i32, @bitCast(root_ptr.byte_offset)))))
            else
                resolveRawWinHandleOpt(sys_st, root_ptr.byte_offset, .reg_key) orelse return try retSigned(vm, ret_ty, 6);
            const subkey_w = try readVmWideStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(subkey_w);
            const sam: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const key_out = argPtr(vm, frame_idx, call_site, 4);
            var opened_key: ?*anyopaque = null;
            const status = advapi32.RegOpenKeyExW(@ptrFromInt(root_bits), subkey_w.ptr, 0, sam, &opened_key);
            if (status == 0 and opened_key != null) {
                const vm_k = try registerWinHandle(vm, .reg_key, @intFromPtr(opened_key.?));
                try vm.writePointerAt(key_out, vm.options.target_layout.ptr_align_log2, vm_k);
            }
            return try retSigned(vm, ret_ty, status);
        },
        .win_reg_query_value_ex_w => {
            const key_ptr = argPtr(vm, frame_idx, call_site, 0);
            const raw_key = resolveRawWinHandleOpt(sys_st, key_ptr.byte_offset, .reg_key) orelse {
                return try retSigned(vm, ret_ty, 6);
            };
            const val_ptr = argPtr(vm, frame_idx, call_site, 1);
            const val_w = if (val_ptr.alloc_id.isNullOrNone()) null else try readVmWideStringZ(vm, val_ptr);
            defer if (val_w) |vw| vm.allocator.free(vw);
            const ty_out = argPtr(vm, frame_idx, call_site, 3);
            const data_out = argPtr(vm, frame_idx, call_site, 4);
            const cb_inout = argPtr(vm, frame_idx, call_site, 5);
            var cb_val: u32 = 0;
            if (!cb_inout.alloc_id.isNullOrNone()) {
                var cb_b: [4]u8 = undefined;
                try vm.readScalarBytes(cb_inout, 0, &cb_b);
                cb_val = std.mem.readInt(u32, &cb_b, .little);
            }
            if (cb_val > 65_536) return error.ResourceLimitExceeded;
            const host_data = vm.allocator.alloc(u8, @max(cb_val, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_data);
            var reg_ty: u32 = 0;
            const status = advapi32.RegQueryValueExW(
                @ptrFromInt(raw_key),
                if (val_w) |vw| vw.ptr else null,
                null,
                &reg_ty,
                if (data_out.alloc_id.isNullOrNone()) null else host_data.ptr,
                if (cb_inout.alloc_id.isNullOrNone()) null else &cb_val,
            );
            if (!ty_out.alloc_id.isNullOrNone()) try writeVmU32(vm, ty_out, reg_ty);
            if (!cb_inout.alloc_id.isNullOrNone()) try writeVmU32(vm, cb_inout, cb_val);
            if (status == 0 and !data_out.alloc_id.isNullOrNone() and cb_val > 0 and cb_val <= host_data.len) {
                try vm.writeScalarBytes(data_out, 0, host_data[0..cb_val]);
            }
            return try retSigned(vm, ret_ty, status);
        },
        .win_reg_close_key => {
            const k_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (k_ptr.alloc_id == vm.dangling_empty_alloc and k_ptr.byte_offset >= HANDLE_SLOT_BASE) {
                const idx: usize = k_ptr.byte_offset - HANDLE_SLOT_BASE;
                if (idx < sys_st.win_handles.items.len and sys_st.win_handles.items[idx].kind == .reg_key) {
                    const raw_bits = sys_st.win_handles.items[idx].raw_bits;
                    sys_st.win_handles.items[idx] = .{};
                    return try retSigned(vm, ret_ty, advapi32.RegCloseKey(@ptrFromInt(raw_bits)));
                }
            }
            return try retSigned(vm, ret_ty, 6);
        },
        else => return null,
    }
}

// -------------------- POSIX Host Dispatch ---------------------

/// Converts a Linux `usize` syscall return into `(isize, errno)` and updates `MirVm` `errno`.
fn finishLinuxSyscall(vm: *MirVm, raw_rc: usize, span: Span) VmEvalError!i64 {
    if (builtin.os.tag != .linux) return -1;
    const signed_rc: isize = @bitCast(raw_rc);
    if (signed_rc < 0 and signed_rc > -4096) {
        _ = try setVmErrno(vm, @intCast(-signed_rc), span);
        return -1;
    }
    return signed_rc;
}

/// Scans `/proc/self/environ` (`<= 1 MiB`) on a Linux host for `key`, returning an owned value slice if present.
fn lookupLinuxHostEnvAlloc(allocator: std.mem.Allocator, key: []const u8) VmEvalError!?[]u8 {
    if (builtin.os.tag != .linux or key.len == 0) return null;
    const opened = std.os.linux.openat(-100, "/proc/self/environ", .{ .ACCMODE = .RDONLY, .CLOEXEC = true }, 0);
    const signed_fd: isize = @bitCast(opened);
    if (signed_fd < 0) return null;
    const env_fd: i32 = @intCast(signed_fd);
    defer _ = std.os.linux.close(env_fd);

    var raw_env: std.ArrayListUnmanaged(u8) = .empty;
    defer raw_env.deinit(allocator);
    var chunk: [4096]u8 = undefined;
    while (raw_env.items.len < 1_048_576) {
        const got_raw = std.os.linux.read(env_fd, &chunk, chunk.len);
        const got_signed: isize = @bitCast(got_raw);
        if (got_signed <= 0) break;
        const got_len: usize = @intCast(got_signed);
        raw_env.appendSlice(allocator, chunk[0..got_len]) catch return error.OutOfMemory;
    }

    var entry_it = std.mem.splitScalar(u8, raw_env.items, 0);
    while (entry_it.next()) |entry| {
        if (entry.len <= key.len or entry[key.len] != '=') continue;
        if (std.mem.eql(u8, entry[0..key.len], key)) {
            return allocator.dupe(u8, entry[key.len + 1 ..]) catch return error.OutOfMemory;
        }
    }
    return null;
}

/// Dispatches a `core.sys.{linux,macos}` `extern "C"` call on a Linux or macOS host.
fn evalPosixHostOp(
    vm: *MirVm,
    frame_idx: usize,
    op: ShimOp,
    call_site: mir.MirCallSite,
    ret_ty: TypeId,
    span: Span,
) VmEvalError!?RegSlot {
    if (builtin.os.tag != .linux and builtin.os.tag != .macos) return null;
    const sys_st = ensureSysState(vm);

    switch (op) {
        .posix_errno_location => {
            if (sys_st.errno_alloc == .none) {
                _ = try setVmErrno(vm, 0, span);
            }
            return retPtr(.{ .alloc_id = sys_st.errno_alloc, .byte_offset = 0 });
        },
        .posix_exit => {
            vm.exited_with_code = @truncate(try argI64(vm, frame_idx, call_site, 0));
            return error.ProcessExited;
        },
        .posix_openat => {
            const dir_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(path_z);
            const flags: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            const mode: u32 = if (call_site.args_len >= 4) @truncate(try argU64(vm, frame_idx, call_site, 3)) else 0;
            const fd_res: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.openat(dir_fd, path_z.ptr, @bitCast(flags), mode), span)
            else blk: {
                const rc = darwin_c.openat(dir_fd, path_z.ptr, flags, @as(c_uint, mode));
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            if (fd_res >= 3) sys_st.posix_open_fds.put(vm.allocator, @intCast(fd_res), {}) catch return error.OutOfMemory;
            return try retSigned(vm, ret_ty, fd_res);
        },
        .posix_write => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const buf_ptr = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            if (byte_len > 0) try vm.readScalarBytes(buf_ptr, 0, host_buf[0..byte_len]);
            if (fd == 1 or fd == 2) {
                const cap_target = if (fd == 1) vm.options.stdout_capture else vm.options.stderr_capture;
                if (cap_target) |cap| {
                    if (byte_len > 0) cap.appendSlice(vm.allocator, host_buf[0..byte_len]) catch return error.OutOfMemory;
                }
                return try retSigned(vm, ret_ty, @intCast(byte_len));
            }
            const wrote: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.write(fd, host_buf.ptr, byte_len), span)
            else blk: {
                const rc = darwin_c.write(fd, host_buf.ptr, byte_len);
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            return try retSigned(vm, ret_ty, wrote);
        },
        .posix_read => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const buf_out = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            const got: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.read(fd, host_buf.ptr, byte_len), span)
            else blk: {
                const rc = darwin_c.read(fd, host_buf.ptr, byte_len);
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            if (got > 0) try vm.writeScalarBytes(buf_out, 0, host_buf[0..@intCast(got)]);
            return try retSigned(vm, ret_ty, got);
        },
        .posix_pread => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const buf_out = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
            const off = try argI64(vm, frame_idx, call_site, 3);
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            const got: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.pread(fd, host_buf.ptr, byte_len, off), span)
            else blk: {
                const rc = darwin_c.pread(fd, host_buf.ptr, byte_len, off);
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            if (got > 0) try vm.writeScalarBytes(buf_out, 0, host_buf[0..@intCast(got)]);
            return try retSigned(vm, ret_ty, got);
        },
        .posix_pwrite => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const buf_ptr = argPtr(vm, frame_idx, call_site, 1);
            const byte_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
            const off = try argI64(vm, frame_idx, call_site, 3);
            if (byte_len > vm.options.mem_limit) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(byte_len, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            if (byte_len > 0) try vm.readScalarBytes(buf_ptr, 0, host_buf[0..byte_len]);
            const wrote: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.pwrite(fd, host_buf.ptr, byte_len, off), span)
            else blk: {
                const rc = darwin_c.pwrite(fd, host_buf.ptr, byte_len, off);
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            return try retSigned(vm, ret_ty, wrote);
        },
        .posix_lseek => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const delta = try argI64(vm, frame_idx, call_site, 1);
            const whence: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            const new_pos: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.lseek(fd, delta, @intCast(whence)), span)
            else blk: {
                const rc = darwin_c.lseek(fd, delta, whence);
                if (rc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk rc;
            };
            return try retSigned(vm, ret_ty, new_pos);
        },
        .posix_ftruncate => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const sz = try argI64(vm, frame_idx, call_site, 1);
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.ftruncate(fd, sz), span)
            else blk: {
                const res = darwin_c.ftruncate(fd, sz);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_fchmod => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const mode: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.fchmod(fd, mode), span)
            else blk: {
                const res = darwin_c.fchmod(fd, @truncate(mode));
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_fsync, .posix_fdatasync => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(
                    vm,
                    if (op == .posix_fdatasync) std.os.linux.fdatasync(fd) else std.os.linux.fsync(fd),
                    span,
                )
            else blk: {
                const res = darwin_c.fsync(fd);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_fcntl => {
            if (builtin.os.tag == .macos) {
                const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const cmd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
                if (cmd == 50) {
                    const out_ptr = argPtr(vm, frame_idx, call_site, 2);
                    var path_buf: [1024]u8 = @splat(0);
                    const res = darwin_c.fcntl(fd, cmd, @as([*]u8, &path_buf));
                    if (res < 0) {
                        _ = try setVmErrno(vm, darwin_c.__error().*, span);
                    } else {
                        const nul_pos = std.mem.indexOfScalar(u8, &path_buf, 0) orelse 1023;
                        try vm.writeScalarBytes(out_ptr, 0, path_buf[0 .. nul_pos + 1]);
                    }
                    return try retSigned(vm, ret_ty, res);
                }
                const arg_i: c_int = if (call_site.args_len >= 3) @truncate(try argI64(vm, frame_idx, call_site, 2)) else 0;
                const res = darwin_c.fcntl(fd, cmd, arg_i);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_close => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            _ = sys_st.posix_open_fds.remove(fd);
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.close(fd), span)
            else blk: {
                const res = darwin_c.close(fd);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_renameat => {
            const old_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const old_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(old_p);
            const new_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            const new_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 3));
            defer vm.allocator.free(new_p);
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.renameat2(old_fd, old_p.ptr, new_fd, new_p.ptr, 0), span)
            else blk: {
                const res = darwin_c.renameat(old_fd, old_p.ptr, new_fd, new_p.ptr);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_unlinkat => {
            const dir_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(path_z);
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.unlinkat(dir_fd, path_z.ptr, flags), span)
            else blk: {
                const res = darwin_c.unlinkat(dir_fd, path_z.ptr, @bitCast(flags));
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_mkdirat => {
            const dir_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(path_z);
            const mode: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.mkdirat(dir_fd, path_z.ptr, mode), span)
            else blk: {
                const res = darwin_c.mkdirat(dir_fd, path_z.ptr, @truncate(mode));
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_linkat => {
            const old_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const old_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(old_p);
            const new_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            const new_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 3));
            defer vm.allocator.free(new_p);
            const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.linkat(old_fd, old_p.ptr, new_fd, new_p.ptr, flags), span)
            else blk: {
                const res = darwin_c.linkat(old_fd, old_p.ptr, new_fd, new_p.ptr, @bitCast(flags));
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_symlinkat => {
            const target_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(target_p);
            const new_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const link_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 2));
            defer vm.allocator.free(link_p);
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.symlinkat(target_p.ptr, new_fd, link_p.ptr), span)
            else blk: {
                const res = darwin_c.symlinkat(target_p.ptr, new_fd, link_p.ptr);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_readlinkat => {
            const dir_fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(path_z);
            const buf_out = argPtr(vm, frame_idx, call_site, 2);
            const cap: usize = @intCast(try argU64(vm, frame_idx, call_site, 3));
            if (cap > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
            const host_buf = vm.allocator.alloc(u8, @max(cap, 1)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            const got: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.readlinkat(dir_fd, path_z.ptr, host_buf.ptr, cap), span)
            else blk: {
                const res = darwin_c.readlinkat(dir_fd, path_z.ptr, host_buf.ptr, cap);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            if (got > 0) try vm.writeScalarBytes(buf_out, 0, host_buf[0..@intCast(got)]);
            return try retSigned(vm, ret_ty, got);
        },
        .posix_getcwd => {
            const buf_out = argPtr(vm, frame_idx, call_site, 0);
            const cap: usize = @intCast(try argU64(vm, frame_idx, call_site, 1));
            if (cap == 0 or cap > MAX_SHIM_PATH_UNITS) {
                _ = try setVmErrno(vm, 22, span);
                return retPtr(SymbolicPtr.NULL);
            }
            const host_buf = vm.allocator.alloc(u8, cap) catch return error.OutOfMemory;
            defer vm.allocator.free(host_buf);
            @memset(host_buf, 0);
            if (builtin.os.tag == .linux) {
                const rc = try finishLinuxSyscall(vm, std.os.linux.getcwd(host_buf.ptr, cap), span);
                if (rc < 0) return retPtr(SymbolicPtr.NULL);
            } else {
                if (darwin_c.getcwd(host_buf.ptr, cap) == null) {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                    return retPtr(SymbolicPtr.NULL);
                }
            }
            const nul_pos = std.mem.indexOfScalar(u8, host_buf, 0) orelse (cap - 1);
            try vm.writeScalarBytes(buf_out, 0, host_buf[0 .. nul_pos + 1]);
            return retPtr(buf_out);
        },
        .posix_chdir => {
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_z);
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.chdir(path_z.ptr), span)
            else blk: {
                const res = darwin_c.chdir(path_z.ptr);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_flock => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const lock_op: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.flock(fd, lock_op), span)
            else blk: {
                const res = darwin_c.flock(fd, lock_op);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_mmap => {
            const map_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 1));
            const prot: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            const map_flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 4));
            const off = try argI64(vm, frame_idx, call_site, 5);
            if (map_len == 0 or map_len > vm.options.mem_limit) {
                _ = try setVmErrno(vm, 22, span);
                return retPtr(invalidWinHandlePtr(vm));
            }
            var host_addr: usize = 0;
            if (builtin.os.tag == .linux) {
                const raw = std.os.linux.mmap(null, map_len, prot, @bitCast(map_flags), fd, @bitCast(off));
                if (try finishLinuxSyscall(vm, raw, span) < 0) return retPtr(invalidWinHandlePtr(vm));
                host_addr = raw;
            } else {
                const mapped = darwin_c.mmap(null, map_len, @bitCast(prot), @bitCast(map_flags), fd, off);
                if (mapped == null or @intFromPtr(mapped.?) == std.math.maxInt(usize)) {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                    return retPtr(invalidWinHandlePtr(vm));
                }
                host_addr = @intFromPtr(mapped.?);
            }
            const is_mut = (prot & 0x02) != 0;
            const alloc_bytes = if (is_mut) map_len else std.mem.alignForward(usize, map_len, 4096);
            if (alloc_bytes > vm.options.mem_limit) {
                if (builtin.os.tag == .linux) {
                    _ = std.os.linux.munmap(@ptrFromInt(host_addr), map_len);
                } else {
                    _ = darwin_c.munmap(@ptrFromInt(host_addr), map_len);
                }
                return error.ResourceLimitExceeded;
            }
            const vm_aid = try vm.allocMemory(alloc_bytes, 4, is_mut, false, true, 0, span);
            const host_slice = @as([*]const u8, @ptrFromInt(host_addr))[0..map_len];
            const alloc_rec = &vm.allocations.items[vm_aid.payloadIndex()];
            @memcpy(alloc_rec.bytes[0..map_len], host_slice);
            @memset(alloc_rec.init_mask, std.math.maxInt(u64));
            sys_st.mapped_views.append(vm.allocator, .{
                .vm_alloc = vm_aid,
                .host_addr = host_addr,
                .byte_len = map_len,
            }) catch return error.OutOfMemory;
            return retPtr(.{ .alloc_id = vm_aid, .byte_offset = 0 });
        },
        .posix_munmap => {
            const view_ptr = argPtr(vm, frame_idx, call_site, 0);
            for (sys_st.mapped_views.items, 0..) |rec, idx| {
                if (rec.vm_alloc == view_ptr.alloc_id and view_ptr.byte_offset == 0) {
                    const rc: i64 = if (builtin.os.tag == .linux)
                        try finishLinuxSyscall(vm, std.os.linux.munmap(@ptrFromInt(rec.host_addr), rec.byte_len), span)
                    else
                        darwin_c.munmap(@ptrFromInt(rec.host_addr), rec.byte_len);
                    vm.allocations.items[rec.vm_alloc.payloadIndex()].is_live = false;
                    _ = sys_st.mapped_views.swapRemove(idx);
                    return try retSigned(vm, ret_ty, rc);
                }
            }
            _ = try setVmErrno(vm, 22, span);
            return try retSigned(vm, ret_ty, -1);
        },
        .posix_isatty => {
            return try retSigned(vm, ret_ty, 0);
        },
        .posix_clock_gettime => {
            const clk_id: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const tp_out = argPtr(vm, frame_idx, call_site, 1);
            if (builtin.os.tag == .linux) {
                var ts: std.os.linux.timespec = .{ .sec = 0, .nsec = 0 };
                const rc = try finishLinuxSyscall(vm, std.os.linux.clock_gettime(@fromBackingInt(@intCast(clk_id)), &ts), span);
                if (rc == 0) {
                    try writeVmI64(vm, tp_out, ts.sec);
                    try writeVmI64(vm, try vm.advanceSymbolicPtr(tp_out, 8), ts.nsec);
                }
                return try retSigned(vm, ret_ty, rc);
            } else {
                var ts: [2]i64 = .{ 0, 0 };
                const res = darwin_c.clock_gettime(clk_id, &ts);
                if (res == 0) {
                    try writeVmI64(vm, tp_out, ts[0]);
                    try writeVmI64(vm, try vm.advanceSymbolicPtr(tp_out, 8), ts[1]);
                } else {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                }
                return try retSigned(vm, ret_ty, res);
            }
        },
        .posix_clock_gettime_nsec_np => {
            if (builtin.os.tag == .macos) {
                const clk_id: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                return try retUnsigned(vm, ret_ty, darwin_c.clock_gettime_nsec_np(clk_id));
            }
            return null;
        },
        .posix_mach_continuous_time => {
            if (builtin.os.tag == .macos) return try retUnsigned(vm, ret_ty, darwin_c.mach_continuous_time());
            return null;
        },
        .posix_mach_timebase_info => {
            if (builtin.os.tag == .macos) {
                var info: [2]u32 = .{ 1, 1 };
                const res = darwin_c.mach_timebase_info(&info);
                const out_ptr = argPtr(vm, frame_idx, call_site, 0);
                try writeVmU32(vm, out_ptr, info[0]);
                try writeVmU32(vm, try vm.advanceSymbolicPtr(out_ptr, 4), info[1]);
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_nanosleep => {
            const req_ptr = argPtr(vm, frame_idx, call_site, 0);
            const rem_ptr = argPtr(vm, frame_idx, call_site, 1);
            const has_rem = !rem_ptr.alloc_id.isNullOrNone();
            var req_b: [16]u8 = undefined;
            try vm.readScalarBytes(req_ptr, 0, &req_b);
            const sec = std.mem.readInt(i64, req_b[0..8], .little);
            const nsec = std.mem.readInt(i64, req_b[8..16], .little);
            if (builtin.os.tag == .linux) {
                var req_ts: std.os.linux.timespec = .{ .sec = @intCast(sec), .nsec = @intCast(nsec) };
                var rem_ts: std.os.linux.timespec = .{ .sec = 0, .nsec = 0 };
                const rc = try finishLinuxSyscall(
                    vm,
                    std.os.linux.nanosleep(&req_ts, if (has_rem) &rem_ts else null),
                    span,
                );
                if (has_rem) {
                    try writeVmI64(vm, rem_ptr, @intCast(rem_ts.sec));
                    try writeVmI64(vm, try vm.advanceSymbolicPtr(rem_ptr, 8), @intCast(rem_ts.nsec));
                }
                return try retSigned(vm, ret_ty, rc);
            } else {
                const req_ts: [2]i64 = .{ sec, nsec };
                var rem_ts: [2]i64 = .{ 0, 0 };
                const res = darwin_c.nanosleep(&req_ts, if (has_rem) &rem_ts else null);
                if (has_rem) {
                    try writeVmI64(vm, rem_ptr, rem_ts[0]);
                    try writeVmI64(vm, try vm.advanceSymbolicPtr(rem_ptr, 8), rem_ts[1]);
                }
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                return try retSigned(vm, ret_ty, res);
            }
        },
        .posix_getpid => {
            const pid: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.getpid(), span)
            else
                darwin_c.getpid();
            return try retSigned(vm, ret_ty, pid);
        },
        .posix_stat, .posix_lstat, .posix_fstat, .posix_fstatat => {
            if (builtin.os.tag == .macos) {
                var stat_buf: [144]u8 align(8) = @splat(0);
                const out_arg_i: usize = if (op == .posix_fstatat) 2 else 1;
                const out_ptr = argPtr(vm, frame_idx, call_site, out_arg_i);
                const res: c_int = switch (op) {
                    .posix_fstat => darwin_c.fstat(@truncate(try argI64(vm, frame_idx, call_site, 0)), &stat_buf),
                    .posix_stat => blk: {
                        const pz = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
                        defer vm.allocator.free(pz);
                        break :blk darwin_c.stat(pz.ptr, &stat_buf);
                    },
                    .posix_lstat => blk: {
                        const pz = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
                        defer vm.allocator.free(pz);
                        break :blk darwin_c.lstat(pz.ptr, &stat_buf);
                    },
                    .posix_fstatat => blk: {
                        const dfd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 0));
                        const pz = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
                        defer vm.allocator.free(pz);
                        const flg: c_int = @truncate(try argI64(vm, frame_idx, call_site, 3));
                        break :blk darwin_c.fstatat(dfd, pz.ptr, &stat_buf, flg);
                    },
                    else => unreachable,
                };
                if (res == 0) {
                    try vm.writeScalarBytes(out_ptr, 0, &stat_buf);
                } else {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                }
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_getdirentries64 => {
            if (builtin.os.tag == .macos) {
                const dir_fd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const buf_out = argPtr(vm, frame_idx, call_site, 1);
                const cap: usize = @intCast(try argU64(vm, frame_idx, call_site, 2));
                const basep_ptr = argPtr(vm, frame_idx, call_site, 3);
                if (cap > 1_048_576) return error.ResourceLimitExceeded;
                var base_b: [8]u8 = undefined;
                try vm.readScalarBytes(basep_ptr, 0, &base_b);
                var base_val = std.mem.readInt(i64, &base_b, .little);
                const host_buf = vm.allocator.alloc(u8, @max(cap, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(host_buf);
                const got = darwin_c.__getdirentries64(dir_fd, host_buf.ptr, cap, &base_val);
                if (got >= 0) {
                    if (got > 0) try vm.writeScalarBytes(buf_out, 0, host_buf[0..@intCast(got)]);
                    try writeVmI64(vm, basep_ptr, base_val);
                } else {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                }
                return try retSigned(vm, ret_ty, got);
            }
            return null;
        },
        .posix_syscall => {
            if (builtin.os.tag != .linux) return null;
            const sys_num = try argI64(vm, frame_idx, call_site, 0);
            const arch_statx: i64 = if (builtin.cpu.arch == .aarch64) 291 else 332;
            const arch_fstatat: i64 = if (builtin.cpu.arch == .aarch64) 79 else 262;
            const arch_getdents64: i64 = if (builtin.cpu.arch == .aarch64) 61 else 217;
            const arch_renameat2: i64 = if (builtin.cpu.arch == .aarch64) 276 else 316;

            if (sys_num == 437) {
                const dir_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 1))));
                const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 2));
                defer vm.allocator.free(path_z);
                var how_buf: [24]u8 align(8) = @splat(0);
                try vm.readScalarBytes(argPtr(vm, frame_idx, call_site, 3), 0, &how_buf);
                const how_sz: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
                const raw = std.os.linux.syscall4(@fromBackingInt(@intCast(437)), dir_fd, @intFromPtr(path_z.ptr), @intFromPtr(&how_buf), how_sz);
                const fd_res = try finishLinuxSyscall(vm, raw, span);
                if (fd_res >= 3) sys_st.posix_open_fds.put(vm.allocator, @intCast(fd_res), {}) catch return error.OutOfMemory;
                return try retSigned(vm, ret_ty, fd_res);
            } else if (sys_num == arch_statx) {
                const dir_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 1))));
                const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 2));
                defer vm.allocator.free(path_z);
                const flags: usize = @intCast(try argU64(vm, frame_idx, call_site, 3));
                const mask: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
                const out_ptr = argPtr(vm, frame_idx, call_site, 5);
                var stx_buf: [256]u8 align(8) = @splat(0);
                const raw = std.os.linux.syscall5(
                    @fromBackingInt(@intCast(arch_statx)),
                    dir_fd,
                    @intFromPtr(path_z.ptr),
                    flags,
                    mask,
                    @intFromPtr(&stx_buf),
                );
                const rc = try finishLinuxSyscall(vm, raw, span);
                if (rc == 0) try vm.writeScalarBytes(out_ptr, 0, &stx_buf);
                return try retSigned(vm, ret_ty, rc);
            } else if (sys_num == arch_fstatat) {
                const dir_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 1))));
                const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 2));
                defer vm.allocator.free(path_z);
                const out_ptr = argPtr(vm, frame_idx, call_site, 3);
                const flags: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
                const stat_sz: usize = if (builtin.cpu.arch == .aarch64) 128 else 144;
                var st_buf: [144]u8 align(8) = @splat(0);
                const raw = std.os.linux.syscall4(
                    @fromBackingInt(@intCast(arch_fstatat)),
                    dir_fd,
                    @intFromPtr(path_z.ptr),
                    @intFromPtr(&st_buf),
                    flags,
                );
                const rc = try finishLinuxSyscall(vm, raw, span);
                if (rc == 0) try vm.writeScalarBytes(out_ptr, 0, st_buf[0..stat_sz]);
                return try retSigned(vm, ret_ty, rc);
            } else if (sys_num == arch_getdents64) {
                const dir_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 1))));
                const buf_out = argPtr(vm, frame_idx, call_site, 2);
                const cap: usize = @intCast(try argU64(vm, frame_idx, call_site, 3));
                if (cap > 1_048_576) return error.ResourceLimitExceeded;
                const host_buf = vm.allocator.alloc(u8, @max(cap, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(host_buf);
                const raw = std.os.linux.syscall3(@fromBackingInt(@intCast(arch_getdents64)), dir_fd, @intFromPtr(host_buf.ptr), cap);
                const got = try finishLinuxSyscall(vm, raw, span);
                if (got > 0) try vm.writeScalarBytes(buf_out, 0, host_buf[0..@intCast(got)]);
                return try retSigned(vm, ret_ty, got);
            } else if (sys_num == arch_renameat2) {
                const old_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 1))));
                const old_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 2));
                defer vm.allocator.free(old_p);
                const new_fd: usize = @bitCast(@as(isize, @truncate(try argI64(vm, frame_idx, call_site, 3))));
                const new_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 4));
                defer vm.allocator.free(new_p);
                const rflags: usize = @intCast(try argU64(vm, frame_idx, call_site, 5));
                const raw = std.os.linux.syscall5(
                    @fromBackingInt(@intCast(arch_renameat2)),
                    old_fd,
                    @intFromPtr(old_p.ptr),
                    new_fd,
                    @intFromPtr(new_p.ptr),
                    rflags,
                );
                return try retSigned(vm, ret_ty, try finishLinuxSyscall(vm, raw, span));
            }
            _ = try setVmErrno(vm, 38, span);
            return try retSigned(vm, ret_ty, -1);
        },
        .posix_dlsym => {
            const sym_name_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(sym_name_z);
            return retPtr(SymbolicPtr.NULL);
        },
        .posix_getenv => {
            const key_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(key_z);
            if (sys_st.posix_env_ptrs.get(key_z)) |cached_ptr| {
                return retPtr(cached_ptr);
            }
            if (builtin.os.tag == .linux) {
                if (try lookupLinuxHostEnvAlloc(vm.allocator, key_z)) |host_val| {
                    defer vm.allocator.free(host_val);
                    const owned_key = vm.allocator.dupe(u8, key_z) catch return error.OutOfMemory;
                    errdefer vm.allocator.free(owned_key);
                    const vm_str = try allocVmCString(vm, host_val, span);
                    sys_st.posix_env_ptrs.put(vm.allocator, owned_key, vm_str) catch return error.OutOfMemory;
                    return retPtr(vm_str);
                }
            } else if (builtin.os.tag == .macos) {
                if (darwin_c.getenv(key_z.ptr)) |val_cstr| {
                    const owned_key = vm.allocator.dupe(u8, key_z) catch return error.OutOfMemory;
                    errdefer vm.allocator.free(owned_key);
                    const vm_str = try allocVmCString(vm, std.mem.span(val_cstr), span);
                    sys_st.posix_env_ptrs.put(vm.allocator, owned_key, vm_str) catch return error.OutOfMemory;
                    return retPtr(vm_str);
                }
            }
            return retPtr(SymbolicPtr.NULL);
        },
        .posix_setenv => {
            const key_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(key_z);
            const val_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
            defer vm.allocator.free(val_z);
            const overwrite: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            if (overwrite == 0) {
                if (sys_st.posix_env_ptrs.get(key_z)) |existing_ptr| {
                    if (!existing_ptr.alloc_id.isNullOrNone()) return try retSigned(vm, ret_ty, 0);
                } else if (builtin.os.tag == .linux) {
                    if (try lookupLinuxHostEnvAlloc(vm.allocator, key_z)) |existing_host| {
                        vm.allocator.free(existing_host);
                        return try retSigned(vm, ret_ty, 0);
                    }
                } else if (builtin.os.tag == .macos) {
                    if (darwin_c.getenv(key_z.ptr) != null) return try retSigned(vm, ret_ty, 0);
                }
            }
            const vm_str = try allocVmCString(vm, val_z, span);
            if (sys_st.posix_env_ptrs.getPtr(key_z)) |slot_ptr| {
                slot_ptr.* = vm_str;
            } else {
                const owned_key = vm.allocator.dupe(u8, key_z) catch return error.OutOfMemory;
                sys_st.posix_env_ptrs.put(vm.allocator, owned_key, vm_str) catch return error.OutOfMemory;
            }
            if (builtin.os.tag == .macos) _ = darwin_c.setenv(key_z.ptr, val_z.ptr, overwrite);
            return try retSigned(vm, ret_ty, 0);
        },
        .posix_unsetenv => {
            const key_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(key_z);
            if (sys_st.posix_env_ptrs.getPtr(key_z)) |slot_ptr| {
                slot_ptr.* = SymbolicPtr.NULL;
            } else {
                const owned_key = vm.allocator.dupe(u8, key_z) catch return error.OutOfMemory;
                sys_st.posix_env_ptrs.put(vm.allocator, owned_key, SymbolicPtr.NULL) catch return error.OutOfMemory;
            }
            if (builtin.os.tag == .macos) _ = darwin_c.unsetenv(key_z.ptr);
            return try retSigned(vm, ret_ty, 0);
        },
        .posix_writev => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const iov_base_ptr = argPtr(vm, frame_idx, call_site, 1);
            const iov_cnt_raw = try argI64(vm, frame_idx, call_site, 2);
            if (iov_cnt_raw <= 0 or iov_cnt_raw > 1024) return try retSigned(vm, ret_ty, 0);
            const iov_cnt: usize = @intCast(iov_cnt_raw);
            const ptr_bytes: u64 = vm.options.target_layout.ptr_byte_size;
            const ptr_align = vm.options.target_layout.ptr_align_log2;
            var total_written: i64 = 0;
            for (0..iov_cnt) |iov_i| {
                const entry_ptr = try vm.advanceSymbolicPtr(iov_base_ptr, @as(u64, @intCast(iov_i)) * ptr_bytes * 2);
                const len_val: usize = @intCast(try readVmUsize(vm, try vm.advanceSymbolicPtr(entry_ptr, ptr_bytes)));
                if (len_val == 0) continue;
                if (len_val > vm.options.mem_limit) return error.ResourceLimitExceeded;
                const data_ptr = try vm.readPointerAt(entry_ptr, ptr_align);
                const seg_buf = vm.allocator.alloc(u8, len_val) catch return error.OutOfMemory;
                defer vm.allocator.free(seg_buf);
                try vm.readScalarBytes(data_ptr, 0, seg_buf);
                if (fd == 1 or fd == 2) {
                    const cap_target = if (fd == 1) vm.options.stdout_capture else vm.options.stderr_capture;
                    if (cap_target) |cap| cap.appendSlice(vm.allocator, seg_buf) catch return error.OutOfMemory;
                    total_written += @intCast(len_val);
                } else {
                    const wrote: i64 = if (builtin.os.tag == .linux)
                        try finishLinuxSyscall(vm, std.os.linux.write(fd, seg_buf.ptr, len_val), span)
                    else
                        darwin_c.write(fd, seg_buf.ptr, len_val);
                    if (wrote < 0) {
                        if (total_written == 0 and builtin.os.tag == .macos) {
                            _ = try setVmErrno(vm, darwin_c.__error().*, span);
                        }
                        return try retSigned(vm, ret_ty, if (total_written > 0) total_written else -1);
                    }
                    total_written += wrote;
                    if (wrote < @as(i64, @intCast(len_val))) break;
                }
            }
            return try retSigned(vm, ret_ty, total_written);
        },
        .posix_readv => {
            const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const iov_base_ptr = argPtr(vm, frame_idx, call_site, 1);
            const iov_cnt_raw = try argI64(vm, frame_idx, call_site, 2);
            if (iov_cnt_raw <= 0 or iov_cnt_raw > 1024) return try retSigned(vm, ret_ty, 0);
            const iov_cnt: usize = @intCast(iov_cnt_raw);
            const ptr_bytes: u64 = vm.options.target_layout.ptr_byte_size;
            const ptr_align = vm.options.target_layout.ptr_align_log2;
            var total_read: i64 = 0;
            for (0..iov_cnt) |iov_i| {
                const entry_ptr = try vm.advanceSymbolicPtr(iov_base_ptr, @as(u64, @intCast(iov_i)) * ptr_bytes * 2);
                const len_val: usize = @intCast(try readVmUsize(vm, try vm.advanceSymbolicPtr(entry_ptr, ptr_bytes)));
                if (len_val == 0) continue;
                if (len_val > vm.options.mem_limit) return error.ResourceLimitExceeded;
                const data_ptr = try vm.readPointerAt(entry_ptr, ptr_align);
                const seg_buf = vm.allocator.alloc(u8, len_val) catch return error.OutOfMemory;
                defer vm.allocator.free(seg_buf);
                const got: i64 = if (builtin.os.tag == .linux)
                    try finishLinuxSyscall(vm, std.os.linux.read(fd, seg_buf.ptr, len_val), span)
                else
                    darwin_c.read(fd, seg_buf.ptr, len_val);
                if (got < 0) {
                    if (total_read == 0 and builtin.os.tag == .macos) {
                        _ = try setVmErrno(vm, darwin_c.__error().*, span);
                    }
                    return try retSigned(vm, ret_ty, if (total_read > 0) total_read else -1);
                }
                if (got == 0) break;
                try vm.writeScalarBytes(data_ptr, 0, seg_buf[0..@intCast(got)]);
                total_read += got;
                if (got < @as(i64, @intCast(len_val))) break;
            }
            return try retSigned(vm, ret_ty, total_read);
        },
        .posix_realpath => {
            const path_z = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 0));
            defer vm.allocator.free(path_z);
            const out_ptr = argPtr(vm, frame_idx, call_site, 1);
            if (builtin.os.tag == .macos) {
                var resolved_buf: [1024]u8 = @splat(0);
                if (darwin_c.realpath(path_z.ptr, &resolved_buf) == null) {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                    return retPtr(SymbolicPtr.NULL);
                }
                const nul_pos = std.mem.indexOfScalar(u8, &resolved_buf, 0) orelse 1023;
                if (out_ptr.alloc_id.isNullOrNone()) return retPtr(try allocVmCString(vm, resolved_buf[0..nul_pos], span));
                try vm.writeScalarBytes(out_ptr, 0, resolved_buf[0 .. nul_pos + 1]);
                return retPtr(out_ptr);
            } else {
                const opened = std.os.linux.openat(-100, path_z.ptr, .{ .ACCMODE = .RDONLY, .PATH = true, .CLOEXEC = true }, 0);
                const fd_rc = try finishLinuxSyscall(vm, opened, span);
                if (fd_rc < 0) return retPtr(SymbolicPtr.NULL);
                defer _ = std.os.linux.close(@intCast(fd_rc));
                var proc_link_buf: [64]u8 = undefined;
                const proc_link = std.fmt.bufPrintZ(&proc_link_buf, "/proc/self/fd/{d}", .{fd_rc}) catch unreachable;
                var resolved_buf: [4096]u8 = @splat(0);
                const rl_rc = try finishLinuxSyscall(vm, std.os.linux.readlinkat(-100, proc_link.ptr, &resolved_buf, 4095), span);
                if (rl_rc < 0) return retPtr(SymbolicPtr.NULL);
                const rlen: usize = @intCast(rl_rc);
                resolved_buf[rlen] = 0;
                if (out_ptr.alloc_id.isNullOrNone()) return retPtr(try allocVmCString(vm, resolved_buf[0..rlen], span));
                try vm.writeScalarBytes(out_ptr, 0, resolved_buf[0 .. rlen + 1]);
                return retPtr(out_ptr);
            }
        },
        .posix_clonefileat => {
            if (builtin.os.tag == .macos) {
                const src_fd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const src_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
                defer vm.allocator.free(src_p);
                const dst_fd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 2));
                const dst_p = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 3));
                defer vm.allocator.free(dst_p);
                const flg: u32 = @truncate(try argU64(vm, frame_idx, call_site, 4));
                const res = darwin_c.clonefileat(src_fd, src_p.ptr, dst_fd, dst_p.ptr, flg);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_fcopyfile => {
            if (builtin.os.tag == .macos) {
                const src_fd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const dst_fd: c_int = @truncate(try argI64(vm, frame_idx, call_site, 1));
                const flg: u32 = @truncate(try argU64(vm, frame_idx, call_site, 3));
                const res = darwin_c.fcopyfile(src_fd, dst_fd, null, flg);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_copy_file_range => {
            if (builtin.os.tag == .linux) {
                const fd_in: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const fd_out: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
                const byte_len: usize = @intCast(try argU64(vm, frame_idx, call_site, 4));
                const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
                const rc = try finishLinuxSyscall(vm, std.os.linux.copy_file_range(fd_in, null, fd_out, null, byte_len, flags), span);
                return try retSigned(vm, ret_ty, rc);
            }
            return null;
        },
        .posix_ioctl => {
            if (builtin.os.tag == .linux) {
                const fd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const req: u32 = @truncate(try argU64(vm, frame_idx, call_site, 1));
                const arg_val: usize = if (call_site.args_len >= 3) @intCast(try argU64(vm, frame_idx, call_site, 2)) else 0;
                const rc = try finishLinuxSyscall(vm, std.os.linux.ioctl(fd, req, arg_val), span);
                return try retSigned(vm, ret_ty, rc);
            }
            return null;
        },
        .posix_inotify_init1 => {
            if (builtin.os.tag == .linux) {
                const flags: u32 = @truncate(try argU64(vm, frame_idx, call_site, 0));
                const fd_res = try finishLinuxSyscall(vm, std.os.linux.inotify_init1(flags), span);
                if (fd_res >= 3) sys_st.posix_open_fds.put(vm.allocator, @intCast(fd_res), {}) catch return error.OutOfMemory;
                return try retSigned(vm, ret_ty, fd_res);
            }
            return null;
        },
        .posix_inotify_add_watch => {
            if (builtin.os.tag == .linux) {
                const ifd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const pz = try readVmCStringZ(vm, argPtr(vm, frame_idx, call_site, 1));
                defer vm.allocator.free(pz);
                const mask: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
                const rc = try finishLinuxSyscall(vm, std.os.linux.inotify_add_watch(ifd, pz.ptr, mask), span);
                return try retSigned(vm, ret_ty, rc);
            }
            return null;
        },
        .posix_inotify_rm_watch => {
            if (builtin.os.tag == .linux) {
                const ifd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const wd: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
                const rc = try finishLinuxSyscall(vm, std.os.linux.inotify_rm_watch(ifd, wd), span);
                return try retSigned(vm, ret_ty, rc);
            }
            return null;
        },
        .posix_kqueue => {
            if (builtin.os.tag == .macos) {
                const kq = darwin_c.kqueue();
                if (kq < 0) {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                } else if (kq >= 3) {
                    sys_st.posix_open_fds.put(vm.allocator, kq, {}) catch return error.OutOfMemory;
                }
                return try retSigned(vm, ret_ty, kq);
            }
            return null;
        },
        .posix_kevent64 => {
            if (builtin.os.tag == .macos) {
                const kq: c_int = @truncate(try argI64(vm, frame_idx, call_site, 0));
                const chg_ptr = argPtr(vm, frame_idx, call_site, 1);
                const nchg: c_int = @truncate(try argI64(vm, frame_idx, call_site, 2));
                const ev_out = argPtr(vm, frame_idx, call_site, 3);
                const nev: c_int = @truncate(try argI64(vm, frame_idx, call_site, 4));
                const flg: u32 = @truncate(try argU64(vm, frame_idx, call_site, 5));
                const to_ptr = argPtr(vm, frame_idx, call_site, 6);
                if (nchg < 0 or nchg > 1024 or nev < 0 or nev > 1024) return error.ResourceLimitExceeded;
                const chg_bytes: usize = @as(usize, @intCast(nchg)) * 48;
                const ev_bytes: usize = @as(usize, @intCast(nev)) * 48;
                const host_chg = vm.allocator.alloc(u8, @max(chg_bytes, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(host_chg);
                if (chg_bytes > 0 and !chg_ptr.alloc_id.isNullOrNone()) try vm.readScalarBytes(chg_ptr, 0, host_chg[0..chg_bytes]);
                const host_ev = vm.allocator.alloc(u8, @max(ev_bytes, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(host_ev);
                var to_buf: [16]u8 align(8) = @splat(0);
                var has_to = false;
                if (!to_ptr.alloc_id.isNullOrNone()) {
                    try vm.readScalarBytes(to_ptr, 0, &to_buf);
                    has_to = true;
                }
                const res = darwin_c.kevent64(
                    kq,
                    if (chg_bytes > 0) host_chg.ptr else null,
                    nchg,
                    if (ev_bytes > 0) host_ev.ptr else null,
                    nev,
                    flg,
                    if (has_to) &to_buf else null,
                );
                if (res < 0) {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                } else if (res > 0 and ev_bytes > 0) {
                    try vm.writeScalarBytes(ev_out, 0, host_ev[0 .. @as(usize, @intCast(res)) * 48]);
                }
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_poll => {
            const fds_ptr = argPtr(vm, frame_idx, call_site, 0);
            const nfds: usize = @intCast(try argU64(vm, frame_idx, call_site, 1));
            const timeout_ms: i32 = @truncate(try argI64(vm, frame_idx, call_site, 2));
            if (nfds > 1024) return error.ResourceLimitExceeded;
            const total_bytes = nfds * 8;
            const host_fds = vm.allocator.alignedAlloc(u8, .@"4", @max(total_bytes, 8)) catch return error.OutOfMemory;
            defer vm.allocator.free(host_fds);
            if (total_bytes > 0) try vm.readScalarBytes(fds_ptr, 0, host_fds[0..total_bytes]);
            const rc: i64 = if (builtin.os.tag == .linux) blk: {
                const pfd_slice: [*]std.os.linux.pollfd = @ptrCast(host_fds.ptr);
                break :blk try finishLinuxSyscall(vm, std.os.linux.poll(pfd_slice, @intCast(nfds), timeout_ms), span);
            } else blk: {
                const res = darwin_c.poll(host_fds.ptr, @intCast(nfds), timeout_ms);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            if (rc >= 0 and total_bytes > 0) try vm.writeScalarBytes(fds_ptr, 0, host_fds[0..total_bytes]);
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_pipe, .posix_pipe2 => {
            const out_ptr = argPtr(vm, frame_idx, call_site, 0);
            if (builtin.os.tag == .linux) {
                const flg: u32 = if (op == .posix_pipe2) @truncate(try argU64(vm, frame_idx, call_site, 1)) else 0;
                var fds: [2]i32 = .{ -1, -1 };
                const rc = try finishLinuxSyscall(vm, std.os.linux.pipe2(&fds, @bitCast(flg)), span);
                if (rc == 0) {
                    try writeVmI32(vm, out_ptr, fds[0]);
                    try writeVmI32(vm, try vm.advanceSymbolicPtr(out_ptr, 4), fds[1]);
                    sys_st.posix_open_fds.put(vm.allocator, fds[0], {}) catch return error.OutOfMemory;
                    sys_st.posix_open_fds.put(vm.allocator, fds[1], {}) catch return error.OutOfMemory;
                }
                return try retSigned(vm, ret_ty, rc);
            } else {
                var fds: [2]c_int = .{ -1, -1 };
                const res = darwin_c.pipe(&fds);
                if (res == 0) {
                    try writeVmI32(vm, out_ptr, fds[0]);
                    try writeVmI32(vm, try vm.advanceSymbolicPtr(out_ptr, 4), fds[1]);
                    sys_st.posix_open_fds.put(vm.allocator, fds[0], {}) catch return error.OutOfMemory;
                    sys_st.posix_open_fds.put(vm.allocator, fds[1], {}) catch return error.OutOfMemory;
                } else {
                    _ = try setVmErrno(vm, darwin_c.__error().*, span);
                }
                return try retSigned(vm, ret_ty, res);
            }
        },
        .posix_ns_get_executable_path => {
            if (builtin.os.tag == .macos) {
                const buf_out = argPtr(vm, frame_idx, call_site, 0);
                const sz_ptr = argPtr(vm, frame_idx, call_site, 1);
                var sz_b: [4]u8 = undefined;
                try vm.readScalarBytes(sz_ptr, 0, &sz_b);
                var cap = std.mem.readInt(u32, &sz_b, .little);
                if (cap > MAX_SHIM_PATH_UNITS) return error.ResourceLimitExceeded;
                const host_buf = vm.allocator.alloc(u8, @max(cap, 1)) catch return error.OutOfMemory;
                defer vm.allocator.free(host_buf);
                const res = darwin_c._NSGetExecutablePath(host_buf.ptr, &cap);
                try writeVmU32(vm, sz_ptr, cap);
                if (res == 0 and !buf_out.alloc_id.isNullOrNone()) {
                    const nul_pos = std.mem.indexOfScalar(u8, host_buf, 0) orelse (@max(cap, 1) - 1);
                    try vm.writeScalarBytes(buf_out, 0, host_buf[0 .. nul_pos + 1]);
                }
                return try retSigned(vm, ret_ty, res);
            }
            return null;
        },
        .posix_waitpid => {
            const child_pid: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const status_ptr = argPtr(vm, frame_idx, call_site, 1);
            const opts: u32 = @truncate(try argU64(vm, frame_idx, call_site, 2));
            var status_val: i32 = 0;
            const rc: i64 = if (builtin.os.tag == .linux) blk: {
                var u_status: u32 = 0;
                const wrc = try finishLinuxSyscall(vm, std.os.linux.wait4(child_pid, &u_status, opts, null), span);
                status_val = @bitCast(u_status);
                break :blk wrc;
            } else blk: {
                var c_status: c_int = 0;
                const wrc = darwin_c.waitpid(child_pid, &c_status, @bitCast(opts));
                if (wrc < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                status_val = c_status;
                break :blk wrc;
            };
            if (rc > 0 and !status_ptr.alloc_id.isNullOrNone()) try writeVmI32(vm, status_ptr, status_val);
            return try retSigned(vm, ret_ty, rc);
        },
        .posix_kill => {
            const pid: i32 = @truncate(try argI64(vm, frame_idx, call_site, 0));
            const sig: i32 = @truncate(try argI64(vm, frame_idx, call_site, 1));
            const rc: i64 = if (builtin.os.tag == .linux)
                try finishLinuxSyscall(vm, std.os.linux.kill(pid, @fromBackingInt(@intCast(sig))), span)
            else blk: {
                const res = darwin_c.kill(pid, sig);
                if (res < 0) _ = try setVmErrno(vm, darwin_c.__error().*, span);
                break :blk res;
            };
            return try retSigned(vm, ret_ty, rc);
        },
        else => return null,
    }
}

// ------------------------------------- PUBLIC API --------------------------------------

/// Evaluates a `.std_core` `extern "C"` call in `MirVm` when `is_oracle_runtime_mode` is active (`null` if unhandled).
pub fn tryEvalStdCoreExternCall(
    vm: *MirVm,
    frame_idx: usize,
    entry: VmCallableEntry,
    call_site: mir.MirCallSite,
    call_span: Span,
) VmEvalError!?RegSlot {
    if (!vm.options.is_oracle_runtime_mode) return null;
    const eff_sym_table = vm.options.sym_table orelse vm.sym_table;
    var sym_idx = entry.symbol_index;
    if (sym_idx.isNone() and !entry.def_id.isNone()) {
        sym_idx = eff_sym_table.def_to_symbol.get(entry.def_id.asInt()) orelse .none;
    }
    if (sym_idx.isNone() or sym_idx.asInt() >= eff_sym_table.symbols.items.len) return null;

    const sym_rec = eff_sym_table.getSymbol(sym_idx).*;
    const link_name = if (sym_rec.contract_flags.has_link_name and sym_rec.link_name_text.len > 0)
        sym_rec.link_name_text
    else
        sym_rec.name_text;
    const op = SHIM_OP_MAP.get(link_name) orelse return null;

    const ret_ty: TypeId = if (vm.pool.getFnSignatureView(sym_rec.type_id)) |sig_view|
        sig_view.ret_ty
    else
        .unit_ty;
    vm.context_op_counter += 1;

    if (op == .rt_get_argc or op == .rt_get_argv) {
        return try evalRuntimeProcessArgs(vm, op, ret_ty, call_span);
    }
    if (try evalWindowsHostOp(vm, frame_idx, op, call_site, ret_ty, call_span)) |win_slot| {
        return win_slot;
    }
    if (try evalPosixHostOp(vm, frame_idx, op, call_site, ret_ty, call_span)) |posix_slot| {
        return posix_slot;
    }
    return null;
}
