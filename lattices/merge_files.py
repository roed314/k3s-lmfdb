from genus import write_header_to_file

def merge_files(fnames, out_fname):
    write_header_to_file(out_fname)
    for fname in fnames:
        with open(fname) as f:
            lines = f.readlines()[3:]
        with open(out_fname, "a") as f:
            f.writelines(lines)
