local overseer = require("overseer")
local actions = require "telescope.actions"
local sorters = require "telescope.sorters"
local action_state = require "telescope.actions.state"
local finders = require "telescope.finders"
local make_entry = require "telescope.make_entry"
local pickers = require "telescope.pickers"
local utils = require "telescope.utils"

local conf = require("telescope.config").values

local source_files = {}
vim.list_extend(source_files, vim.split(vim.fn.glob("dk/*.dk"), "\n"))
vim.list_extend(source_files, vim.split(vim.fn.glob("*.lean"), "\n"))
vim.list_extend(source_files, vim.split(vim.fn.glob("Dedukti/**/*.lean"), "\n"))
vim.list_extend(source_files, vim.split(vim.fn.glob("fixtures/**/*.lean"), "\n"))

local prev_trans_file = vim.fn.stdpath("data") .. "/" .. "prev_trans.json"
local prev_trans = vim.fn.filereadable(prev_trans_file) ~= 0 and vim.fn.json_decode(vim.fn.readfile(prev_trans_file)) or {}
local curr_trans_file

-- choose the most recently translated file
local max_ts = 0
for prev, time in pairs(prev_trans) do
  if time > max_ts then
    curr_trans_file = prev
    max_ts = time
  end
end

local templates = {
  ["translate"] = {
    builder = function(params)
      return {
        cmd = { "lake" },
        args = { "run", "trans", params.file },
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  },
  ["translate only"] = {
    builder = function(params)
      return {
        cmd = { "lake" },
        args = { "run", "trans", params.file, "--print", "--write", "--only", params.only},
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  },
  ["check"] = {
    builder = function()
      return {
        cmd = { "lake" },
        args = { "run", "check"},
        components = {
          { "restart_on_save", paths = source_files},
          "default",
        },
      }
    end,
  }
}

local function region_to_text()
  local _, ls, cs = unpack(vim.fn.getpos('v'))
  local _, le, ce = unpack(vim.fn.getpos('.'))
  local swap = ls > le or (ls == le and cs > ce)
  ls, cs, le, ce = unpack(swap and {le, ce, ls, cs} or {ls, cs, le, ce})
  local text = vim.api.nvim_buf_get_text(0, ls-1, cs-1, le-1, ce, {})[1]
  return text
end

local curr_task, curr_task_win

local abort_curr_task = function ()
  if curr_task then
    if vim.api.nvim_win_is_valid(curr_task_win) then
      vim.api.nvim_win_close(curr_task_win, true)
    end
    overseer.run_action(curr_task, "unwatch")
    curr_task:dispose()
  end
end

local function task_split (task)
  abort_curr_task()

  local main_win = vim.api.nvim_get_current_win()
  overseer.run_action(task, "open vsplit")
  curr_task_win = vim.api.nvim_get_current_win()
  vim.cmd("wincmd L")
  vim.cmd("wincmd 90|")
  vim.cmd("set winfixwidth")
  vim.cmd("set wrap")

  vim.api.nvim_set_current_win(main_win)
  curr_task = task
end


local prev_onlys_file = vim.fn.stdpath("data") .. "/" .. "prev_onlys.json"
local prev_onlys = vim.fn.filereadable(prev_onlys_file) ~= 0 and vim.fn.json_decode(vim.fn.readfile(prev_onlys_file)) or {}
local last_template
local last_params = {}

local function run_template(name, params)
  last_template = name
  last_params = params or {}
  overseer.run_template({name = name, params = params}, task_split)
end

local function resume_prev_template()
  if not last_template then print("no previous template run, aborting...") return end
  run_template(last_template, last_params)
end

local function run_only(only)
  prev_onlys[only] = os.time()
  local json = vim.fn.json_encode(prev_onlys)
  vim.fn.writefile({json}, prev_onlys_file)
  run_template("translate only", {only = only, file = curr_trans_file})
end

local function choose_trans(trans_file)
  prev_trans[trans_file] = os.time()
  local json = vim.fn.json_encode(prev_trans)
  vim.fn.writefile({json}, prev_trans_file)
  curr_trans_file = trans_file
end

local transfile_picker = function(opts)
  opts = opts or {}

  local results = {}

  for _, file in ipairs(vim.fn.split(vim.fn.glob("fixtures/**/*.lean"), "\n")) do
    file = vim.loop.fs_realpath(file)
    if file ~= curr_trans_file then
      table.insert(results, file)
    end
  end

  return pickers
    .new(opts, {
      prompt_title = string.format("Choose file to translate (current: %s)", vim.fn.fnamemodify(curr_trans_file, ":t")),
      finder = finders.new_table {
        results = results,
        entry_maker = opts.entry_maker or make_entry.gen_from_file(opts),
      },
      sorter = sorters.Sorter:new {
        discard = true,

        scoring_function = function(_, _, line)
          return prev_trans[line] and -prev_trans[line] or 0
        end,
      },
      previewer = conf.grep_previewer(opts),
      attach_mappings = function(prompt_bufnr)
        actions.select_default:replace(function()
          local selection = action_state.get_selected_entry()

          actions.close(prompt_bufnr)
          choose_trans(selection.value)
          if last_template == "translate" or last_template == "translate only" then
            run_template(last_template, vim.tbl_extend("keep", {file = curr_trans_file}, last_params))
          end
        end)

        return true
      end,
    })
end

local only_picker = function(opts) return pickers
    .new(opts, {
      prompt_title = "previous --only args",
      finder = finders.new_table {
        results = (function()
          local onlys = {}
          for only, _ in pairs(prev_onlys) do
            table.insert(onlys, only)
          end
          return onlys
        end)(),

        entry_maker = function(entry)
          return make_entry.set_default_entry_mt({
            value = entry,
            ordinal = entry,
            display = entry,
          })
        end
      },
      sorter = sorters.Sorter:new {
        discard = true,

        scoring_function = function(_, prompt, line)
          return -prev_onlys[line]
        end,
      },
      attach_mappings = function(prompt_bufnr)
        actions.select_default:replace(function()
          local selection = action_state.get_selected_entry()
          if selection == nil then
            utils.__warn_no_selection "--only args"
            return
          end

          actions.close(prompt_bufnr)
          local val = selection.value
          run_only(val)
        end)

        return true
      end,
    })
end

for name, template in pairs(templates) do
  template.name = name
  overseer.register_template(template)
end

vim.keymap.set("n", "<leader>tt", function () run_template("translate", {file = curr_trans_file}) end)
vim.keymap.set("n", "<leader>tc", function () run_template("check", {}) end)
vim.keymap.set("n", "<leader>to", function () run_only(vim.fn.input("enter constant names (comma-separated, no whitespace): ")) end)
vim.keymap.set("v", "<leader>to", function () run_only(region_to_text()) end)
vim.keymap.set("n", "<leader>tO", function () only_picker():find() end)
vim.keymap.set("n", "<leader>tf", function () transfile_picker():find() end)
vim.keymap.set("n", "<leader>tq", function () abort_curr_task() end)
vim.keymap.set("n", "<leader>t<Tab>", function () resume_prev_template() end)
