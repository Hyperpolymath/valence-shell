defmodule VSH.Filesystem do
  @moduledoc """
  Valence Shell - Elixir Filesystem Operations

  This module implements filesystem operations matching the Coq specification
  in proofs/coq/filesystem_model.v and proofs/coq/file_operations.v

  ## Correspondence with Formal Model

  Coq Specification → Elixir Implementation:
  - `safe_mkdir` → `mkdir/2`
  - `safe_rmdir` → `rmdir/2`
  - `safe_create_file` → `create_file/2`
  - `safe_delete_file` → `delete_file/2`

  ## Verification Status

  ✓ Specification formally verified in Coq
  ✓ Error conditions match POSIX model
  ❌ Implementation NOT formally verified
  → Requires manual review or testing to ensure correctness

  ## Trust Model

  This implementation should be tested against the formal specification.
  For production use, consider:
  - Property-based testing (using extracted Coq as oracle)
  - Audit logging for MAA compliance
  - Runtime assertion of preconditions
  """

  @type path :: [String.t()]
  @type error :: :eexist | :enoent | :eacces | :enotdir | :eisdir | :enotempty | :einval
  @type result(t) :: {:ok, t} | {:error, error}

  defmodule State do
    @moduledoc """
    Audit state for MAA (Mutually Assured Accountability)

    Tracks all filesystem operations for later proof generation.
    """
    defstruct [
      audit_log: [],
      proof_certificates: %{}
    ]
  end

  ## POSIX-style Operations with Error Handling

  @doc """
  Create a directory (safe version matching Coq `safe_mkdir`)

  ## Preconditions (from Coq):
  - Path does not exist
  - Parent directory exists
  - Parent is a directory
  - Parent has write permission

  ## Returns
  - `{:ok, :created}` if successful
  - `{:error, reason}` matching POSIX errors

  ## Examples

      iex> VSH.Filesystem.mkdir(["tmp", "test_dir"])
      {:ok, :created}

      iex> VSH.Filesystem.mkdir(["tmp", "test_dir"])
      {:error, :eexist}
  """
  @spec mkdir(path, keyword) :: result(:created)
  def mkdir(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # EEXIST: path already exists
      File.exists?(path_str) ->
        {:error, :eexist}

      # ENOENT: parent doesn't exist
      not File.exists?(parent_str) ->
        {:error, :enoent}

      # ENOTDIR: parent is not a directory
      not File.dir?(parent_str) ->
        {:error, :enotdir}

      # EACCES: parent not writable (simplified check)
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to create
      true ->
        case File.mkdir(path_str) do
          :ok ->
            maybe_audit(:mkdir, path, opts)
            {:ok, :created}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Remove a directory (safe version matching Coq `safe_rmdir`)

  ## Preconditions (from Coq):
  - Path exists and is a directory
  - Directory is empty
  - Parent has write permission
  - Not root directory

  ## Returns
  - `{:ok, :removed}` if successful
  - `{:error, reason}` matching POSIX errors
  """
  @spec rmdir(path, keyword) :: result(:removed)
  def rmdir(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # ENOENT: path doesn't exist
      not File.exists?(path_str) ->
        {:error, :enoent}

      # ENOTDIR: path is not a directory
      not File.dir?(path_str) ->
        {:error, :enotdir}

      # ENOTEMPTY: directory not empty
      not empty_dir?(path_str) ->
        {:error, :enotempty}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # EACCES: cannot remove root
      path == [] ->
        {:error, :eacces}

      # Preconditions satisfied - safe to remove
      true ->
        case File.rmdir(path_str) do
          :ok ->
            maybe_audit(:rmdir, path, opts)
            {:ok, :removed}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Create a file (safe version matching Coq `safe_create_file`)

  ## Preconditions (from Coq):
  - Path does not exist
  - Parent directory exists
  - Parent is a directory
  - Parent has write permission
  """
  @spec create_file(path, keyword) :: result(:created)
  def create_file(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # EEXIST: path already exists
      File.exists?(path_str) ->
        {:error, :eexist}

      # ENOENT: parent doesn't exist
      not File.exists?(parent_str) ->
        {:error, :enoent}

      # ENOTDIR: parent is not a directory
      not File.dir?(parent_str) ->
        {:error, :enotdir}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to create
      true ->
        case File.write(path_str, "") do
          :ok ->
            maybe_audit(:create_file, path, opts)
            {:ok, :created}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  @doc """
  Delete a file (safe version matching Coq `safe_delete_file`)

  ## Preconditions (from Coq):
  - Path exists and is a file
  - Parent has write permission
  """
  @spec delete_file(path, keyword) :: result(:removed)
  def delete_file(path, opts \\ []) do
    path_str = path_to_string(path)
    parent_str = path_to_string(parent_path(path))

    cond do
      # ENOENT: path doesn't exist
      not File.exists?(path_str) ->
        {:error, :enoent}

      # EISDIR: path is a directory
      File.dir?(path_str) ->
        {:error, :eisdir}

      # EACCES: parent not writable
      not writable?(parent_str) ->
        {:error, :eacces}

      # Preconditions satisfied - safe to delete
      true ->
        case File.rm(path_str) do
          :ok ->
            maybe_audit(:delete_file, path, opts)
            {:ok, :removed}
          {:error, reason} ->
            {:error, posix_to_error(reason)}
        end
    end
  end

  ## Reversible Operations (MAA Framework)

  @doc """
  Reversible directory creation - returns undo function

  This implements the RMR (Remove-Match-Reverse) primitive proven in Coq.

  ## Example

      iex> {result, undo} = VSH.Filesystem.mkdir_reversible(["tmp", "test"])
      iex> result
      {:ok, :created}
      iex> undo.()
      {:ok, :removed}
  """
  def mkdir_reversible(path, opts \\ []) do
    case mkdir(path, opts) do
      {:ok, :created} = result ->
        undo = fn -> rmdir(path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  @doc """
  Reversible file creation - returns undo function

  This implements the RMR primitive for files, proven in Coq.
  """
  def create_file_reversible(path, opts \\ []) do
    case create_file(path, opts) do
      {:ok, :created} = result ->
        undo = fn -> delete_file(path, opts) end
        {result, undo}
      error ->
        {error, fn -> error end}
    end
  end

  ## Path Utilities

  @doc """
  Convert path list to string

  Matches Coq path model: Path = list PathComponent
  """
  @spec path_to_string(path) :: String.t()
  def path_to_string([]), do: "/"
  def path_to_string(components), do: "/" <> Enum.join(components, "/")

  @doc """
  Get parent path

  Matches Coq `parent_path` function
  """
  @spec parent_path(path) :: path
  def parent_path([]), do: []
  def parent_path(path) do
    path
    |> Enum.reverse()
    |> tl()
    |> Enum.reverse()
  rescue
    _ -> []
  end

  ## Helper Functions

  defp empty_dir?(path_str) do
    case File.ls(path_str) do
      {:ok, []} -> true
      _ -> false
    end
  end

  defp writable?(path_str) do
    case File.stat(path_str) do
      {:ok, %{access: access}} when access in [:read_write, :write] -> true
      _ -> false
    end
  end

  defp posix_to_error(:eexist), do: :eexist
  defp posix_to_error(:enoent), do: :enoent
  defp posix_to_error(:eacces), do: :eacces
  defp posix_to_error(:enotdir), do: :enotdir
  defp posix_to_error(:eisdir), do: :eisdir
  defp posix_to_error(:enotempty), do: :enotempty
  defp posix_to_error(_), do: :einval

  defp maybe_audit(operation, path, opts) do
    if opts[:audit] do
      # In production: write to audit log with timestamp and proof certificate
      IO.puts("[AUDIT] #{operation} #{inspect(path)}")
    end
  end
end
